const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const Compilation = @import("../Compilation.zig");
const Diagnostic = @import("../Diagnostic.zig");
const IR = @import("../IR.zig");
const Literal = @import("../Literal.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Resolve = @import("Resolve.zig");
const Narrow = @import("Narrow.zig");
const Flow = @import("Flow.zig");
const Aggregate = @import("Aggregate.zig");
const Place = @import("Place.zig");

const Closest = Diagnostic.Closest;
const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;
const Value = Typer.Value;
const refOf = Typer.refOf;

pub fn checkIdent(typer: *Typer, node: Node.Index) Allocator.Error!Value {
    const comp = typer.comp;
    const text = typer.mainTokenText(node);

    if (Module.isDiscard(text)) {
        try typer.failDiscard(node);
        return .poison;
    }

    if (typer.findLocalIndex(text)) |index| {
        const local = typer.localAt(index);
        if (local.kind == .var_slot) return typer.emitOneValue(node, .load, local.type, local.ref);
        if (Narrow.activeNarrow(typer, .{ .local = index })) |narrow| {
            return Narrow.valueOfRef(narrow.ref, narrow.type);
        }
        return Narrow.valueOfRef(local.ref, local.type);
    }

    for (typer.bindings) |binding| {
        if (comp.pool.sameText(binding.name, text)) return .{ .named_type = binding.type };
    }
    if (Pool.primitiveType(text)) |primitive| return .{ .named_type = primitive };
    if (Resolve.visibleDecl(typer, text)) |decl_index| {
        if (Narrow.activeNarrow(typer, .{ .decl = decl_index })) |narrow| {
            return Narrow.valueOfRef(narrow.ref, narrow.type);
        }
        return Resolve.declAsValue(typer, decl_index, node);
    }

    try typer.reportUndefined(node, text);
    return .poison;
}

pub fn checkNumber(typer: *Typer, node: Node.Index) Allocator.Error!Value {
    const comp = typer.comp;
    switch (try Literal.decodeNumber(comp.arena.allocator(), typer.mainTokenText(node))) {
        .int => |value| return typer.untypedInt(value),
        .float => |value| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_float = .{ .type = .untyped_float_type, .value = value },
        }) },
        .refused => |refusal| return typer.refuse(node, refusal),
    }
}

pub fn checkString(typer: *Typer, node: Node.Index) Allocator.Error!Value {
    const comp = typer.comp;
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var reading = Literal.bytesOf(typer.mainTokenText(node));
    while (reading.next()) |piece| switch (piece) {
        .bytes => |run| try appendText(typer, run),
        .refused => |refusal| return typer.refuse(node, refusal),
    };
    return textValue(typer, mark);
}

pub fn checkMultilineString(typer: *Typer, view: AST.View.MultilineString) Allocator.Error!Value {
    const comp = typer.comp;
    assert(view.last.int() >= view.first.int());
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var line = view.first;
    while (true) : (line = line.after(1)) {
        assert(typer.tree.tokenTag(line) == .string_line);
        if (line != view.first) try appendText(typer, "\n");
        try appendText(typer, Literal.textLine(typer.tree.tokenSlice(line)));
        if (line == view.last) break;
    }
    return textValue(typer, mark);
}

/// Bytes, so a string never lands on a wider element than it spells.
fn appendText(typer: *Typer, run: []const u8) Allocator.Error!void {
    const comp = typer.comp;
    const before = comp.pool.scratch.items.len;
    // interning touches the pool's items, never its scratch, so the reservation holds
    try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, run.len);
    for (run) |byte| {
        comp.pool.scratch.appendAssumeCapacity(try comp.pool.int(comp.gpa, .u8_type, byte));
    }
    assert(comp.pool.scratch.items.len == before + run.len);
}

fn textValue(typer: *Typer, mark: usize) Allocator.Error!Value {
    const comp = typer.comp;
    assert(comp.pool.scratch.items.len >= mark);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = .untyped_aggregate_type,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

pub fn checkChar(typer: *Typer, node: Node.Index) Allocator.Error!Value {
    switch (Literal.decodeChar(typer.mainTokenText(node))) {
        .codepoint => |value| return typer.untypedInt(value),
        .refused => |refusal| return typer.refuse(node, refusal),
    }
}

const Operation = struct {
    node: Node.Index,
    op: AST.BinaryOp,
    op_token: Token.Index,
    lhs: Value,
    lhs_node: Node.Index,
    rhs: Value,
    rhs_node: Node.Index,
};

pub fn checkBinary(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.Binary,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    if (view.op == .bool_and) return Flow.checkShortCircuit(typer, node, view);
    if (view.op == .bool_or) return Flow.checkOr(typer, view, hint);

    const lhs = try typer.checkValue(view.lhs, null);
    const rhs = try typer.checkValue(view.rhs, null);
    if (lhs == .diverged or rhs == .diverged) return .diverged;
    if (lhs == .poison or rhs == .poison) return .poison;
    return combine(typer, .{
        .node = node,
        .op = view.op,
        .op_token = view.op_token,
        .lhs = lhs,
        .lhs_node = view.lhs,
        .rhs = rhs,
        .rhs_node = view.rhs,
    });
}

pub fn combine(typer: *Typer, it: Operation) Allocator.Error!Value {
    const comp = typer.comp;
    assert(it.op != .bool_and);
    assert(it.op != .bool_or);

    if (it.lhs == .constant and it.rhs == .constant) {
        const folded = try comp.pool.fold(comp.gpa, it.op, it.lhs.constant, it.rhs.constant);
        return settleFold(typer, it.lhs_node, it.op_token, folded);
    }
    return emitBinary(typer, it);
}

fn settleFold(
    typer: *Typer,
    node: Node.Index,
    op_token: Token.Index,
    folded: Pool.Fold,
) Allocator.Error!Value {
    const comp = typer.comp;
    const report: Diagnostic.Report = switch (folded) {
        .value => |value| return .{ .constant = value },
        .truth => |holds| return typer.settledTruth(node, holds),
        .overflow => .{
            .code = .overflow,
            .message = "this overflows the 128 bits constants fold in",
            .label = "too large",
        },
        .division_by_zero => .{
            .code = .division_by_zero,
            .message = "this divides by zero",
            .label = "the divisor is zero",
        },
        .bad_shift => |bad| .{
            .code = .bad_shift,
            .message = try comp.fmt("{s} shifts by 0 to {d}, and this shifts by {d}", .{
                try comp.typeName(bad.type),
                Pool.widthOf(bad.type) - 1,
                bad.count,
            }),
            .label = "not a shift count",
        },
        .does_not_fit => |missed| try typer.doesNotFit(missed.value, missed.type, null),
        .mismatch => |pair| {
            try failMixedTypes(typer, op_token, pair.left, pair.right, operand_help);
            return .poison;
        },
        .bad_operand => |operand_type| {
            try reportBadOperand(typer, op_token, operand_type);
            return .poison;
        },
    };
    return typer.refuseToken(op_token, report);
}

const operand_help = "nothing converts on its own, so give both sides one type";

pub fn failMixedTypes(
    typer: *Typer,
    op_token: Token.Index,
    left: Pool.Index,
    right: Pool.Index,
    help: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.failToken(op_token, .{
        .code = .mixed_types,
        .message = try typer.comp.fmt("'{s}' mixes {s} and {s}", .{
            typer.tree.tokenSlice(op_token),
            try typer.comp.typeName(left),
            try typer.comp.typeName(right),
        }),
        .label = "two different types",
        .help = help,
    });
}

fn emitBinary(typer: *Typer, it: Operation) Allocator.Error!Value {
    const pool = &typer.comp.pool;
    const lhs_type = typer.typeOf(it.lhs);
    const rhs_type = typer.typeOf(it.rhs);
    const left = Pool.sharedType(lhs_type, rhs_type) orelse {
        const union_side: ?Pool.Index = if (pool.isUnion(lhs_type))
            lhs_type
        else if (pool.isUnion(rhs_type))
            rhs_type
        else
            null;
        const equality = it.op == .equal or it.op == .not_equal;
        const help = if (union_side) |side|
            operandHelp(typer, side, equality) orelse operand_help
        else
            operand_help;
        try failMixedTypes(typer, it.op_token, lhs_type, rhs_type, help);
        return .poison;
    };

    const lhs = try typer.coerce(it.lhs, left, it.lhs_node);
    const rhs = try typer.coerce(it.rhs, left, it.rhs_node);
    if (lhs == .poison or rhs == .poison) return .poison;

    const how = loweringOf(it.op);
    const admissible = switch (how.takes) {
        .number => Pool.isNumeric(left),
        .whole => Pool.isInteger(left),
        .scalar => Pool.isNumeric(left) or typer.comp.pool.keyOf(left) == .type_pointer,
    };
    if (admissible == false) {
        try reportBadOperand(typer, it.op_token, left);
        return .poison;
    }

    const result_type = if (how.compares) try typer.boolType(it.lhs_node) else left;
    return typer.emitValue(it.node, .ofBinary(it.op), result_type, .{
        .bin = .{ .lhs = refOf(lhs), .rhs = refOf(rhs) },
    });
}

const Lowering = struct { takes: enum { number, whole, scalar } = .number, compares: bool = false };

fn loweringOf(op: AST.BinaryOp) Lowering {
    return switch (op) {
        .add, .sub, .mul, .div => .{},
        .mod, .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => .{ .takes = .whole },
        .equal, .not_equal => .{ .takes = .scalar, .compares = true },
        .less_than, .less_or_equal, .greater_than, .greater_or_equal => .{ .compares = true },
        // control flow, lowered as branches by `checkShortCircuit` and `checkOr`
        .bool_and, .bool_or => unreachable,
    };
}

pub fn checkUnary(typer: *Typer, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = typer.comp;
    if (view.op == .address_of) return Place.checkAddressOf(typer, node, view);

    const operand = try typer.checkValue(view.operand, null);
    if (operand.stops()) return operand;
    const bools = if (view.op == .bool_not) try typer.boolType(view.operand) else .poison;

    if (operand == .constant) {
        const folded: Pool.Fold = switch (view.op) {
            .negate => try comp.pool.foldNegate(comp.gpa, operand.constant),
            .bit_not => try comp.pool.foldBitNot(comp.gpa, operand.constant),
            .bool_not => not: {
                if (bools == .poison) break :not .{ .value = .poison };
                const truth = typer.truthOf(bools, operand.constant) orelse
                    break :not .{ .bad_operand = typer.typeOf(operand) };
                break :not .{ .truth = !truth };
            },
            .address_of => unreachable,
        };
        return settleFold(typer, view.operand, view.op_token, folded);
    }

    const found = typer.typeOf(operand);
    switch (view.op) {
        .negate => {
            if (Pool.isSignedNumber(found) == false) {
                return reportBadUnary(typer, view, found, "needs a signed number");
            }
            return typer.emitOneValue(node, .negate, found, refOf(operand));
        },
        .bit_not => {
            if (Pool.isInteger(found) == false) {
                return reportBadUnary(typer, view, found, "needs an integer");
            }
            return typer.emitOneValue(node, .bit_not, found, refOf(operand));
        },
        .bool_not => {
            const met = try typer.coerce(operand, bools, view.operand);
            if (met == .poison) return .poison;
            return typer.emitOneValue(node, .not, bools, refOf(met));
        },
        .address_of => unreachable,
    }
}

fn reportBadUnary(
    typer: *Typer,
    view: AST.View.Unary,
    found: Pool.Index,
    wants: []const u8,
) Allocator.Error!Value {
    return typer.refuseToken(view.op_token, .{
        .code = .bad_operand,
        .message = try typer.comp.fmt("'{s}' {s}, and this is {s}", .{
            typer.tree.tokenSlice(view.op_token),
            wants,
            try typer.comp.typeName(found),
        }),
        .label = "wrong operand type",
    });
}

pub fn checkFieldAccess(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.FieldAccess,
) Allocator.Error!Value {
    const comp = typer.comp;
    const base = try typer.checkExpr(view.lhs, null);
    switch (base) {
        .poison => return .poison,
        .diverged => return .diverged,
        .named_module => |target| {
            const member = try Resolve.exported(typer, target, node, view.name_token) orelse return .poison;
            return Resolve.declAsValue(typer, member, node);
        },
        .named_type, .named_generic => {
            return typer.refuse(node, .{
                .code = .not_a_function,
                .message = try comp.fmt("'{s}' is reached through a value or called, " ++
                    "and cannot be read", .{typer.tree.tokenSlice(view.name_token)}),
                .label = "not a value",
            });
        },
        .named_fn => {
            try failFieldOnFunction(typer, view.name_token);
            return .poison;
        },
        .constant, .runtime => return valueField(typer, node, view, base),
    }
}

fn valueField(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.FieldAccess,
    base: Value,
) Allocator.Error!Value {
    const comp = typer.comp;
    const reached = try reachField(typer, typer.typeOf(base), view.name_token) orelse return .poison;
    const row = switch (reached.member) {
        .field => |row| row,
        .method => unreachable,
        .length => |length| {
            const count = length orelse {
                const held = try viewValue(typer, node, base, reached);
                return typer.emitOneValue(node, .slice_len, .u64_type, held);
            };
            return .{ .constant = try comp.pool.int(comp.gpa, .u64_type, count) };
        },
        .address => |slice| {
            const held = try viewValue(typer, node, base, reached);
            const result = try typer.pointerTo(slice.child, slice.mutable);
            return typer.emitOneValue(node, .slice_ptr, result, held);
        },
    };
    const row_type = comp.rowAt(row).type;

    if (reached.pointer == null and base == .constant and
        comp.pool.keyOf(base.constant) == .value_aggregate)
    {
        const rows = comp.instanceAt(comp.pool.structOf(reached.owner)).rows;
        return .{ .constant = comp.pool.aggregateAt(base.constant, row.int() - rows.start) };
    }

    const operand: IR.Inst.Data = .{ .field = .{ .base = refOf(base), .row = row } };
    if (reached.pointer) |it| {
        const field_pointer = try typer.pointerTo(row_type, it.mutable);
        const place = try typer.emit(node, .field_ptr, field_pointer, operand);
        return typer.emitOneValue(node, .load, row_type, place);
    }
    return typer.emitValue(node, .field_val, row_type, operand);
}

fn viewValue(typer: *Typer, node: Node.Index, base: Value, reached: Reach) Allocator.Error!Ref {
    if (reached.pointer == null) return refOf(base);
    return typer.emitOne(node, .load, reached.owner, refOf(base));
}

const Member = union(enum) {
    field: Compilation.Row.Index,
    method: Decl.Index,
    length: ?u64,
    address: Pool.Key.Slice,

    const Kind = enum { field, method };
};

const length_name = "len";

const address_name = "ptr";

fn memberOf(typer: *Typer, owner: Pool.Index, name: []const u8) Allocator.Error!?Member {
    switch (typer.comp.pool.keyOf(owner)) {
        .type_array => |array| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = array.len };
            return null;
        },
        .type_slice => |view| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = null };
            if (std.mem.eql(u8, name, address_name)) return .{ .address = view };
            return null;
        },
        .type_struct => |instance| return structMember(typer, instance, name),
        else => return null,
    }
}

pub fn structMember(typer: *Typer, instance: Pool.Instance, name: []const u8) Allocator.Error!?Member {
    const comp = typer.comp;
    try comp.ensureRows(instance);
    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        if (comp.pool.sameText(comp.rowAt(.from(raw)).name, name)) return .{ .field = .from(raw) };
    }
    const members = comp.declAt(comp.instanceDecl(instance)).answer.members;
    for (members.start..members.end()) |raw| {
        const member = comp.declAt(.from(raw));
        if (member.kind != .fn_decl) continue;
        if (comp.pool.sameText(member.name, name)) return .{ .method = .from(raw) };
    }
    return null;
}

pub const deref_help = "'.*' reads what a pointer points at, and a field is reached with '.name'";

pub fn pointerAt(
    typer: *Typer,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
    help: ?[]const u8,
) Allocator.Error!?Pool.Key.Pointer {
    switch (typer.comp.pool.keyOf(found)) {
        .type_pointer => |it| return it,
        else => {},
    }
    try typer.fail(node, .{
        .code = .type_mismatch,
        .message = try typer.comp.fmt("'{s}' needs a pointer, and this is {s}", .{
            what,
            try typer.comp.typeName(found),
        }),
        .label = "not a pointer",
        .help = help,
    });
    return null;
}

const Peeled = struct { pointer: ?Pool.Key.Pointer, owner: Pool.Index };

pub fn peelPointer(pool: *const Pool, from: Pool.Index) Peeled {
    switch (pool.keyOf(from)) {
        .type_pointer => |it| return .{ .pointer = it, .owner = it.child },
        else => return .{ .pointer = null, .owner = from },
    }
}

const Reach = struct { pointer: ?Pool.Key.Pointer, owner: Pool.Index, member: Member };

pub fn reachField(typer: *Typer, from: Pool.Index, name_token: Token.Index) Allocator.Error!?Reach {
    const peeled = peelPointer(&typer.comp.pool, from);
    if (try memberOf(typer, peeled.owner, typer.tree.tokenSlice(name_token))) |member| {
        if (member == .field) {
            const owner = typer.comp.pool.structOf(peeled.owner);
            if (try fieldIsVisible(typer, owner, member.field, name_token) == false) return null;
        }
        if (member != .method) return .{
            .pointer = peeled.pointer,
            .owner = peeled.owner,
            .member = member,
        };
    }
    try reportNoMember(typer, peeled.owner, name_token, .field);
    return null;
}

pub fn methodOf(typer: *Typer, owner: Pool.Index, name_token: Token.Index) Allocator.Error!?Decl.Index {
    if (try memberOf(typer, owner, typer.tree.tokenSlice(name_token))) |member| {
        if (member == .method) return member.method;
    }
    try reportNoMember(typer, owner, name_token, .method);
    return null;
}

pub const narrow_help = "a 'let' narrows where a branch proves what it holds, so copy a 'var' " ++
    "or a field into one first";

pub fn reportNoMember(
    typer: *Typer,
    owner: Pool.Index,
    name_token: Token.Index,
    wanted: Member.Kind,
) Allocator.Error!void {
    const comp = typer.comp;
    const name_text = typer.tree.tokenSlice(name_token);
    if (owner == .poison) return;

    if (owner == .untyped_aggregate_type) {
        return typer.failToken(name_token, .{
            .code = .no_such_member,
            .message = "this array has no type yet, so it has no members to reach",
            .label = "no type in sight",
            .help = Aggregate.not_landed_help,
        });
    }

    if (comp.pool.isUnion(owner)) {
        return typer.failToken(name_token, .{
            .code = .not_narrowed,
            .message = try comp.fmt("{s} is a union, and reaching '{s}' means narrowing " ++
                "it first", .{
                try comp.typeName(owner), name_text,
            }),
            .label = "not narrowed",
            .help = narrow_help,
        });
    }

    if (try memberOf(typer, owner, name_text)) |other| {
        const what: []const u8 = switch (other) {
            .method => try comp.fmt("a function, so call it with '.{s}(...)'", .{name_text}),
            .field => "a field, so it is read rather than called",
            .length => "a length, so it is read rather than called",
            .address => "the address a view holds, so it is read rather than called",
        };
        return typer.failToken(name_token, .{
            .code = .no_such_member,
            .message = try comp.fmt("'{s}' is {s}", .{ name_text, what }),
            .label = try comp.fmt("not a {t}", .{wanted}),
        });
    }

    try typer.failToken(name_token, .{
        .code = .no_such_member,
        .message = try comp.fmt("{s} has no {t} named '{s}'", .{
            try comp.typeName(owner), wanted, name_text,
        }),
        .label = try comp.fmt("no such {t}", .{wanted}),
        .help = try suggestMember(typer, owner, name_text),
    });
}

pub fn failNotUnion(
    typer: *Typer,
    node: Node.Index,
    found: Pool.Index,
    asks: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .not_a_union,
        .message = try typer.comp.fmt("{s}, and this is {s}", .{
            asks,
            try typer.comp.typeName(found),
        }),
        .label = "not a union",
    });
}

pub fn failNotMember(
    typer: *Typer,
    node: Node.Index,
    member: Pool.Index,
    union_type: Pool.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .not_a_member,
        .message = try typer.comp.fmt("'{s}' is not a member of '{s}'", .{
            try typer.comp.typeName(member),
            try typer.comp.typeName(union_type),
        }),
        .label = "not a member",
    });
}

pub fn failFieldOnFunction(typer: *Typer, name_token: Token.Index) Allocator.Error!void {
    @branchHint(.cold);
    try typer.failToken(name_token, .{
        .code = .no_such_member,
        .message = "a function has no fields, so call it first",
        .label = "'.' on a function",
    });
}

fn suggestMember(
    typer: *Typer,
    owner: Pool.Index,
    name_text: []const u8,
) Allocator.Error!?[]const u8 {
    const comp = typer.comp;
    var closest: Closest = .{ .target = name_text };

    switch (comp.pool.keyOf(owner)) {
        .type_array => {
            if (std.mem.eql(u8, name_text, address_name)) {
                return "slice it to make a view of it, as in 'a[0..].ptr'";
            }
            closest.consider(length_name);
        },
        .type_slice => {
            closest.consider(length_name);
            closest.consider(address_name);
        },
        .type_struct => |instance| {
            for (comp.instanceRows(instance)) |row| {
                closest.consider(comp.pool.stringText(row.name));
            }
            const members = comp.declAt(comp.instanceDecl(instance)).answer.members;
            for (members.slice(comp.decls.items)) |member| {
                if (member.kind == .fn_decl) closest.consider(comp.pool.stringText(member.name));
            }
        },
        else => return null,
    }
    return closest.didYouMean(comp.arena.allocator());
}

pub fn memberIsVisible(typer: *Typer, member: Decl.Index, at: Token.Index) Allocator.Error!bool {
    const decl = typer.comp.declAt(member);
    if (decl.module == typer.module_index) return true;
    if (Module.declIsPub(typer.comp, member)) return true;

    try failPrivate(typer, at, decl.module, decl.node);
    return false;
}

fn fieldIsVisible(
    typer: *Typer,
    owner: Pool.Instance,
    row: Compilation.Row.Index,
    at: Token.Index,
) Allocator.Error!bool {
    const comp = typer.comp;
    const rows = comp.instanceAt(owner).rows;
    assert(row.int() >= rows.start);
    assert(row.int() < rows.end());

    const decl = comp.declAt(comp.instanceDecl(owner));
    if (decl.module == typer.module_index) return true;
    const node = comp.rowAt(row).node;
    if (comp.treeOf(decl.module).viewOf(node).field.is_pub) return true;

    try failPrivate(typer, at, decl.module, node);
    return false;
}

fn failPrivate(
    typer: *Typer,
    at: Token.Index,
    module: Module.Index,
    node: Node.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(module != typer.module_index);
    assert(typer.tree.tokenTag(at) == .ident);
    try typer.failToken(at, .{
        .code = .private,
        .message = try typer.comp.fmt("'{s}' is private to its file", .{
            typer.tree.tokenSlice(at),
        }),
        .label = "not public",
        .help = "mark it 'pub' to reach it from another file",
        .notes = try typer.comp.noteOne(module, node, "declared here"),
    });
}

fn reportBadOperand(
    typer: *Typer,
    op_token: Token.Index,
    operand_type: Pool.Index,
) Allocator.Error!void {
    const tag = typer.tree.tokenTag(op_token);
    const equality = tag == .eq_eq or tag == .bang_eq;
    try typer.failToken(op_token, .{
        .code = .bad_operand,
        .message = try typer.comp.fmt("'{s}' cannot be applied to {s}", .{
            typer.tree.tokenSlice(op_token),
            try typer.comp.typeName(operand_type),
        }),
        .label = "wrong operand type",
        .help = operandHelp(typer, operand_type, equality),
    });
}

fn operandHelp(typer: *const Typer, found: Pool.Index, equality: bool) ?[]const u8 {
    const pool = &typer.comp.pool;
    if (pool.isUnion(found)) {
        if (equality) return "'is' tests which member a union holds and narrows the name to it";
        for (pool.unionMembers(found)) |member| {
            if (Pool.isNumeric(member) or pool.keyOf(member) == .type_pointer) {
                return "narrow it first, with 'match' or a guard 'is T or return', " ++
                    "and never through a 'var'";
            }
        }
        return null;
    }
    if (equality == false) return null;
    return switch (typer.comp.pool.keyOf(found)) {
        .type_slice => "'mem.equal' compares two views element by element",
        .type_array => "slice them first, as in 'mem.equal(a[0..], b[0..])'",
        .type_struct => "compare the fields that decide it",
        else => null,
    };
}
