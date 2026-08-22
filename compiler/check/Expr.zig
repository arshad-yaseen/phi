const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Check = @import("../Check.zig");
const Compilation = @import("../Compilation.zig");
const Diagnostic = @import("../Diagnostic.zig");
const IR = @import("../IR.zig");
const Literal = @import("../Literal.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Resolve = @import("Resolve.zig");
const Narrowing = @import("Narrowing.zig");
const Flow = @import("Flow.zig");
const Aggregate = @import("Aggregate.zig");
const Place = @import("Place.zig");

const Closest = Diagnostic.Closest;
const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;
const Value = Check.Value;
const refOf = Check.refOf;

pub fn checkIdent(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    const text = check.mainTokenText(node);

    if (Module.isDiscard(text)) {
        try check.failDiscard(node);
        return .poison;
    }

    if (check.findLocalIndex(text)) |index| {
        const local = check.localAt(index);
        if (local.kind == .var_slot) return check.emitOneValue(node, .load, local.type, local.ref);
        if (Narrowing.activeNarrow(check, .{ .local = index })) |narrow| {
            return Narrowing.valueOfRef(narrow.ref, narrow.type);
        }
        return Narrowing.valueOfRef(local.ref, local.type);
    }

    for (check.bindings) |binding| {
        if (comp.pool.sameText(binding.name, text)) return .{ .named_type = binding.type };
    }
    if (Pool.primitiveType(text)) |primitive| return .{ .named_type = primitive };
    if (Resolve.visibleDecl(check, text)) |decl_index| {
        if (Narrowing.activeNarrow(check, .{ .decl = decl_index })) |narrow| {
            return Narrowing.valueOfRef(narrow.ref, narrow.type);
        }
        return Resolve.declAsValue(check, decl_index, node);
    }

    try check.reportUndefined(node, text);
    return .poison;
}

pub fn checkNumber(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    switch (try Literal.decodeNumber(comp.arena.allocator(), check.mainTokenText(node))) {
        .int => |value| return check.untypedInt(value),
        .float => |value| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_float = .{ .type = .untyped_float_type, .value = value },
        }) },
        .refused => |refusal| return check.refuse(node, refusal),
    }
}

pub fn checkString(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var reading = Literal.bytesOf(check.mainTokenText(node));
    while (reading.next()) |piece| switch (piece) {
        .bytes => |run| try appendText(check, run),
        .refused => |refusal| return check.refuse(node, refusal),
    };
    return textValue(check, mark);
}

pub fn checkMultilineString(check: *Check, view: AST.View.MultilineString) Allocator.Error!Value {
    const comp = check.comp;
    assert(view.last.int() >= view.first.int());
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var line = view.first;
    while (true) : (line = line.after(1)) {
        assert(check.tree.tokenTag(line) == .string_line);
        if (line != view.first) try appendText(check, "\n");
        try appendText(check, Literal.textLine(check.tree.tokenSlice(line)));
        if (line == view.last) break;
    }
    return textValue(check, mark);
}

/// Bytes, so a string never lands on a wider element than it spells.
fn appendText(check: *Check, run: []const u8) Allocator.Error!void {
    const comp = check.comp;
    const before = comp.pool.scratch.items.len;
    // interning touches the pool's items, never its scratch, so the reservation holds
    try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, run.len);
    for (run) |byte| {
        comp.pool.scratch.appendAssumeCapacity(try comp.pool.int(comp.gpa, .u8_type, byte));
    }
    assert(comp.pool.scratch.items.len == before + run.len);
}

fn textValue(check: *Check, mark: usize) Allocator.Error!Value {
    const comp = check.comp;
    assert(comp.pool.scratch.items.len >= mark);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = .untyped_aggregate_type,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

pub fn checkChar(check: *Check, node: Node.Index) Allocator.Error!Value {
    switch (Literal.decodeChar(check.mainTokenText(node))) {
        .codepoint => |value| return check.untypedInt(value),
        .refused => |refusal| return check.refuse(node, refusal),
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
    check: *Check,
    node: Node.Index,
    view: AST.View.Binary,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    if (view.op == .bool_and) return Flow.checkShortCircuit(check, node, view);
    if (view.op == .bool_or) return Flow.checkOr(check, view, hint);

    const lhs = try check.checkValue(view.lhs, null);
    const rhs = try check.checkValue(view.rhs, null);
    if (lhs == .diverged or rhs == .diverged) return .diverged;
    if (lhs == .poison or rhs == .poison) return .poison;
    return combine(check, .{
        .node = node,
        .op = view.op,
        .op_token = view.op_token,
        .lhs = lhs,
        .lhs_node = view.lhs,
        .rhs = rhs,
        .rhs_node = view.rhs,
    });
}

pub fn combine(check: *Check, it: Operation) Allocator.Error!Value {
    const comp = check.comp;
    assert(it.op != .bool_and);
    assert(it.op != .bool_or);

    if (it.lhs == .constant and it.rhs == .constant) {
        const folded = try comp.pool.fold(comp.gpa, it.op, it.lhs.constant, it.rhs.constant);
        return settleFold(check, it.lhs_node, it.op_token, folded);
    }
    return emitBinary(check, it);
}

fn settleFold(
    check: *Check,
    node: Node.Index,
    op_token: Token.Index,
    folded: Pool.Fold,
) Allocator.Error!Value {
    const comp = check.comp;
    const report: Diagnostic.Report = switch (folded) {
        .value => |value| return .{ .constant = value },
        .truth => |holds| return check.settledTruth(node, holds),
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
        .does_not_fit => |missed| try check.doesNotFit(missed.value, missed.type, null),
        .mismatch => |pair| {
            try failMixedTypes(check, op_token, pair.left, pair.right, operand_help);
            return .poison;
        },
        .bad_operand => |operand_type| {
            try reportBadOperand(check, op_token, operand_type);
            return .poison;
        },
    };
    return check.refuseToken(op_token, report);
}

const operand_help = "nothing converts on its own, so give both sides one type";

pub fn failMixedTypes(
    check: *Check,
    op_token: Token.Index,
    left: Pool.Index,
    right: Pool.Index,
    help: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.failToken(op_token, .{
        .code = .mixed_types,
        .message = try check.comp.fmt("'{s}' mixes {s} and {s}", .{
            check.tree.tokenSlice(op_token),
            try check.comp.typeName(left),
            try check.comp.typeName(right),
        }),
        .label = "two different types",
        .help = help,
    });
}

fn emitBinary(check: *Check, it: Operation) Allocator.Error!Value {
    const pool = &check.comp.pool;
    const lhs_type = check.typeOf(it.lhs);
    const rhs_type = check.typeOf(it.rhs);
    const left = Pool.sharedType(lhs_type, rhs_type) orelse {
        const union_side: ?Pool.Index = if (pool.isUnion(lhs_type))
            lhs_type
        else if (pool.isUnion(rhs_type))
            rhs_type
        else
            null;
        const equality = it.op == .equal or it.op == .not_equal;
        const help = if (union_side) |side|
            operandHelp(check, side, equality) orelse operand_help
        else
            operand_help;
        try failMixedTypes(check, it.op_token, lhs_type, rhs_type, help);
        return .poison;
    };

    const lhs = try check.coerce(it.lhs, left, it.lhs_node);
    const rhs = try check.coerce(it.rhs, left, it.rhs_node);
    if (lhs == .poison or rhs == .poison) return .poison;

    const how = loweringOf(it.op);
    const admissible = switch (how.takes) {
        .number => Pool.isNumeric(left),
        .whole => Pool.isInteger(left),
        .scalar => Pool.isNumeric(left) or check.comp.pool.keyOf(left) == .type_pointer,
    };
    if (admissible == false) {
        try reportBadOperand(check, it.op_token, left);
        return .poison;
    }

    const result_type = if (how.compares) try check.boolType(it.lhs_node) else left;
    return check.emitValue(it.node, .ofBinary(it.op), result_type, .{
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

pub fn checkUnary(check: *Check, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = check.comp;
    if (view.op == .address_of) return Place.checkAddressOf(check, node, view);

    const operand = try check.checkValue(view.operand, null);
    if (operand.stops()) return operand;
    const bools = if (view.op == .bool_not) try check.boolType(view.operand) else .poison;

    if (operand == .constant) {
        const folded: Pool.Fold = switch (view.op) {
            .negate => try comp.pool.foldNegate(comp.gpa, operand.constant),
            .bit_not => try comp.pool.foldBitNot(comp.gpa, operand.constant),
            .bool_not => not: {
                if (bools == .poison) break :not .{ .value = .poison };
                const truth = check.truthOf(bools, operand.constant) orelse
                    break :not .{ .bad_operand = check.typeOf(operand) };
                break :not .{ .truth = !truth };
            },
            .address_of => unreachable,
        };
        return settleFold(check, view.operand, view.op_token, folded);
    }

    const found = check.typeOf(operand);
    switch (view.op) {
        .negate => {
            if (Pool.isSignedNumber(found) == false) {
                return reportBadUnary(check, view, found, "needs a signed number");
            }
            return check.emitOneValue(node, .negate, found, refOf(operand));
        },
        .bit_not => {
            if (Pool.isInteger(found) == false) {
                return reportBadUnary(check, view, found, "needs an integer");
            }
            return check.emitOneValue(node, .bit_not, found, refOf(operand));
        },
        .bool_not => {
            const met = try check.coerce(operand, bools, view.operand);
            if (met == .poison) return .poison;
            return check.emitOneValue(node, .not, bools, refOf(met));
        },
        .address_of => unreachable,
    }
}

fn reportBadUnary(
    check: *Check,
    view: AST.View.Unary,
    found: Pool.Index,
    wants: []const u8,
) Allocator.Error!Value {
    return check.refuseToken(view.op_token, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'{s}' {s}, and this is {s}", .{
            check.tree.tokenSlice(view.op_token),
            wants,
            try check.comp.typeName(found),
        }),
        .label = "wrong operand type",
    });
}

pub fn checkFieldAccess(
    check: *Check,
    node: Node.Index,
    view: AST.View.FieldAccess,
) Allocator.Error!Value {
    const comp = check.comp;
    const base = try check.checkExpr(view.lhs, null);
    switch (base) {
        .poison => return .poison,
        .diverged => return .diverged,
        .named_module => |target| {
            const member = try Resolve.exported(check, target, node, view.name_token) orelse return .poison;
            return Resolve.declAsValue(check, member, node);
        },
        .named_type, .named_generic => {
            return check.refuse(node, .{
                .code = .not_a_function,
                .message = try comp.fmt("'{s}' is reached through a value or called, " ++
                    "and cannot be read", .{check.tree.tokenSlice(view.name_token)}),
                .label = "not a value",
            });
        },
        .named_fn => {
            try failFieldOnFunction(check, view.name_token);
            return .poison;
        },
        .constant, .runtime => return valueField(check, node, view, base),
    }
}

fn valueField(
    check: *Check,
    node: Node.Index,
    view: AST.View.FieldAccess,
    base: Value,
) Allocator.Error!Value {
    const comp = check.comp;
    const reached = try reachField(check, check.typeOf(base), view.name_token) orelse return .poison;
    const row = switch (reached.member) {
        .field => |row| row,
        .method => unreachable,
        .length => |length| {
            const count = length orelse {
                const held = try viewValue(check, node, base, reached);
                return check.emitOneValue(node, .slice_len, .u64_type, held);
            };
            return .{ .constant = try comp.pool.int(comp.gpa, .u64_type, count) };
        },
        .address => |slice| {
            const held = try viewValue(check, node, base, reached);
            const result = try check.pointerTo(slice.child, slice.mutable);
            return check.emitOneValue(node, .slice_ptr, result, held);
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
        const field_pointer = try check.pointerTo(row_type, it.mutable);
        const place = try check.emit(node, .field_ptr, field_pointer, operand);
        return check.emitOneValue(node, .load, row_type, place);
    }
    return check.emitValue(node, .field_val, row_type, operand);
}

fn viewValue(check: *Check, node: Node.Index, base: Value, reached: Reach) Allocator.Error!Ref {
    if (reached.pointer == null) return refOf(base);
    return check.emitOne(node, .load, reached.owner, refOf(base));
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

fn memberOf(check: *Check, owner: Pool.Index, name: []const u8) Allocator.Error!?Member {
    switch (check.comp.pool.keyOf(owner)) {
        .type_array => |array| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = array.len };
            return null;
        },
        .type_slice => |view| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = null };
            if (std.mem.eql(u8, name, address_name)) return .{ .address = view };
            return null;
        },
        .type_struct => |instance| return structMember(check, instance, name),
        else => return null,
    }
}

pub fn structMember(check: *Check, instance: Pool.Instance, name: []const u8) Allocator.Error!?Member {
    const comp = check.comp;
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
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
    help: ?[]const u8,
) Allocator.Error!?Pool.Key.Pointer {
    switch (check.comp.pool.keyOf(found)) {
        .type_pointer => |it| return it,
        else => {},
    }
    try check.fail(node, .{
        .code = .type_mismatch,
        .message = try check.comp.fmt("'{s}' needs a pointer, and this is {s}", .{
            what,
            try check.comp.typeName(found),
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

pub fn reachField(check: *Check, from: Pool.Index, name_token: Token.Index) Allocator.Error!?Reach {
    const peeled = peelPointer(&check.comp.pool, from);
    if (try memberOf(check, peeled.owner, check.tree.tokenSlice(name_token))) |member| {
        if (member == .field) {
            const owner = check.comp.pool.structOf(peeled.owner);
            if (try fieldIsVisible(check, owner, member.field, name_token) == false) return null;
        }
        if (member != .method) return .{
            .pointer = peeled.pointer,
            .owner = peeled.owner,
            .member = member,
        };
    }
    try reportNoMember(check, peeled.owner, name_token, .field);
    return null;
}

pub fn methodOf(check: *Check, owner: Pool.Index, name_token: Token.Index) Allocator.Error!?Decl.Index {
    if (try memberOf(check, owner, check.tree.tokenSlice(name_token))) |member| {
        if (member == .method) return member.method;
    }
    try reportNoMember(check, owner, name_token, .method);
    return null;
}

pub const narrow_help = "a 'let' narrows where a branch proves what it holds, so copy a 'var' " ++
    "or a field into one first";

pub fn reportNoMember(
    check: *Check,
    owner: Pool.Index,
    name_token: Token.Index,
    wanted: Member.Kind,
) Allocator.Error!void {
    const comp = check.comp;
    const name_text = check.tree.tokenSlice(name_token);
    if (owner == .poison) return;

    if (owner == .untyped_aggregate_type) {
        return check.failToken(name_token, .{
            .code = .no_such_member,
            .message = "this array has no type yet, so it has no members to reach",
            .label = "no type in sight",
            .help = Aggregate.not_landed_help,
        });
    }

    if (comp.pool.isUnion(owner)) {
        return check.failToken(name_token, .{
            .code = .not_narrowed,
            .message = try comp.fmt("{s} is a union, and reaching '{s}' means narrowing " ++
                "it first", .{
                try comp.typeName(owner), name_text,
            }),
            .label = "not narrowed",
            .help = narrow_help,
        });
    }

    if (try memberOf(check, owner, name_text)) |other| {
        const what: []const u8 = switch (other) {
            .method => try comp.fmt("a function, so call it with '.{s}(...)'", .{name_text}),
            .field => "a field, so it is read rather than called",
            .length => "a length, so it is read rather than called",
            .address => "the address a view holds, so it is read rather than called",
        };
        return check.failToken(name_token, .{
            .code = .no_such_member,
            .message = try comp.fmt("'{s}' is {s}", .{ name_text, what }),
            .label = try comp.fmt("not a {t}", .{wanted}),
        });
    }

    try check.failToken(name_token, .{
        .code = .no_such_member,
        .message = try comp.fmt("{s} has no {t} named '{s}'", .{
            try comp.typeName(owner), wanted, name_text,
        }),
        .label = try comp.fmt("no such {t}", .{wanted}),
        .help = try suggestMember(check, owner, name_text),
    });
}

pub fn failNotUnion(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    asks: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .not_a_union,
        .message = try check.comp.fmt("{s}, and this is {s}", .{
            asks,
            try check.comp.typeName(found),
        }),
        .label = "not a union",
    });
}

pub fn failNotMember(
    check: *Check,
    node: Node.Index,
    member: Pool.Index,
    union_type: Pool.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .not_a_member,
        .message = try check.comp.fmt("'{s}' is not a member of '{s}'", .{
            try check.comp.typeName(member),
            try check.comp.typeName(union_type),
        }),
        .label = "not a member",
    });
}

pub fn failFieldOnFunction(check: *Check, name_token: Token.Index) Allocator.Error!void {
    @branchHint(.cold);
    try check.failToken(name_token, .{
        .code = .no_such_member,
        .message = "a function has no fields, so call it first",
        .label = "'.' on a function",
    });
}

fn suggestMember(
    check: *Check,
    owner: Pool.Index,
    name_text: []const u8,
) Allocator.Error!?[]const u8 {
    const comp = check.comp;
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

pub fn memberIsVisible(check: *Check, member: Decl.Index, at: Token.Index) Allocator.Error!bool {
    const decl = check.comp.declAt(member);
    if (decl.module == check.module_index) return true;
    if (Module.declIsPub(check.comp, member)) return true;

    try failPrivate(check, at, decl.module, decl.node);
    return false;
}

fn fieldIsVisible(
    check: *Check,
    owner: Pool.Instance,
    row: Compilation.Row.Index,
    at: Token.Index,
) Allocator.Error!bool {
    const comp = check.comp;
    const rows = comp.instanceAt(owner).rows;
    assert(row.int() >= rows.start);
    assert(row.int() < rows.end());

    const decl = comp.declAt(comp.instanceDecl(owner));
    if (decl.module == check.module_index) return true;
    const node = comp.rowAt(row).node;
    if (comp.treeOf(decl.module).viewOf(node).field.is_pub) return true;

    try failPrivate(check, at, decl.module, node);
    return false;
}

fn failPrivate(
    check: *Check,
    at: Token.Index,
    module: Module.Index,
    node: Node.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(module != check.module_index);
    assert(check.tree.tokenTag(at) == .ident);
    try check.failToken(at, .{
        .code = .private,
        .message = try check.comp.fmt("'{s}' is private to its file", .{
            check.tree.tokenSlice(at),
        }),
        .label = "not public",
        .help = "mark it 'pub' to reach it from another file",
        .notes = try check.comp.noteOne(module, node, "declared here"),
    });
}

fn reportBadOperand(
    check: *Check,
    op_token: Token.Index,
    operand_type: Pool.Index,
) Allocator.Error!void {
    const tag = check.tree.tokenTag(op_token);
    const equality = tag == .eq_eq or tag == .bang_eq;
    try check.failToken(op_token, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'{s}' cannot be applied to {s}", .{
            check.tree.tokenSlice(op_token),
            try check.comp.typeName(operand_type),
        }),
        .label = "wrong operand type",
        .help = operandHelp(check, operand_type, equality),
    });
}

fn operandHelp(check: *const Check, found: Pool.Index, equality: bool) ?[]const u8 {
    const pool = &check.comp.pool;
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
    return switch (check.comp.pool.keyOf(found)) {
        .type_slice => "'mem.equal' compares two views element by element",
        .type_array => "slice them first, as in 'mem.equal(a[0..], b[0..])'",
        .type_struct => "compare the fields that decide it",
        else => null,
    };
}
