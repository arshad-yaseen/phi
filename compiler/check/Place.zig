const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Check = @import("../Check.zig");
const Diagnostic = @import("../Diagnostic.zig");
const IR = @import("../IR.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Narrowing = @import("Narrowing.zig");
const Expr = @import("Expr.zig");
const Aggregate = @import("Aggregate.zig");

const Node = AST.Node;
const Ref = IR.Ref;
const Value = Check.Value;
const refOf = Check.refOf;
const runtimeValue = Check.runtimeValue;

kind: Kind,
/// The address for `.address`, the value itself for `.value`.
ref: Ref,
type: Pool.Index,
node: Node.Index,
/// Why the place cannot be written, null where it can.
immutable: ?Reason,
root_name: []const u8,
root_node: Node.Index,

const Place = @This();

pub fn checkAddressOf(check: *Check, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = check.comp;
    if (check.builder == null) return check.needRuntime(node, "taking an address");

    const place = try checkPlace(check, view.operand) orelse return .poison;
    if (check.typeCanHold(place.type) == false) {
        return check.refuseToken(view.op_token, .{
            .code = .type_mismatch,
            .message = try comp.fmt("'&' needs a value with a type, and this is {s}", .{
                try comp.typeName(place.type),
            }),
            .label = "nothing to point at",
            .help = "give the value a type first, as in 'let n: i64 = 10'",
        });
    }
    const addressed = try placeAddress(check, place) orelse return .poison;
    return runtimeValue(addressed.ref, try check.pointerTo(addressed.type, addressed.mutable()));
}

pub fn checkDeref(check: *Check, node: Node.Index) Allocator.Error!Value {
    const place = try checkPlace(check, node) orelse return .poison;
    return runtimeValue(try placeValue(check, place), place.type);
}

pub const Kind = enum { address, value };
pub const Reason = union(enum) {
    let_bound,
    param_bound,
    read_only: Crossed,
    temporary,
};

pub const Crossed = struct { form: enum { pointer, slice }, child: Pool.Index };

pub fn mutable(place: Place) bool {
    return place.immutable == null;
}

pub fn crossing(place: Place, writable: bool, crossed: Crossed) Place {
    var beyond = place;
    beyond.immutable = if (writable) null else .{ .read_only = crossed };
    return beyond;
}

pub fn reaching(place: Place, node: Node.Index, ref: Ref, type_index: Pool.Index) Place {
    var reached = place;
    reached.kind = .address;
    reached.ref = ref;
    reached.type = type_index;
    reached.node = node;
    return reached;
}

pub fn crossedType(check: *Check, crossed: Place.Crossed, writable: bool) Allocator.Error!Pool.Index {
    return switch (crossed.form) {
        .pointer => check.pointerTo(crossed.child, writable),
        .slice => check.sliceOf(crossed.child, writable),
    };
}

fn localPlace(
    check: *const Check,
    node: Node.Index,
    index: Check.Builder.Local.Index,
    text: []const u8,
) Place {
    const local = check.localAt(index);
    const narrow = Narrowing.activeNarrow(check, .{ .local = index });
    if (narrow != null) assert(local.kind != .var_slot);
    return .{
        .kind = if (local.kind == .var_slot) .address else .value,
        .ref = if (narrow) |it| it.ref else local.ref,
        .type = if (narrow) |it| it.type else local.type,
        .node = node,
        .immutable = switch (local.kind) {
            .var_slot => null,
            .let => .let_bound,
            .param => .param_bound,
        },
        .root_name = text,
        .root_node = local.node,
    };
}

pub fn checkPlace(check: *Check, node: Node.Index) Allocator.Error!?Place {
    if (check.builder == null) {
        const value = try check.checkExpr(node, null);
        return placeOfValue(check, node, value, null);
    }

    switch (check.tree.viewOf(node)) {
        .ident => {
            const text = check.mainTokenText(node);
            if (Module.isDiscard(text)) {
                try check.failDiscard(node);
                return null;
            }
            if (check.findLocalIndex(text)) |index| {
                if (check.localAt(index).type == .poison) return null;
                return localPlace(check, node, index, text);
            }
            const value = try check.checkExpr(node, null);
            return placeOfValue(check, node, value, text);
        },
        .field_access => |access| {
            const base = try checkPlace(check, access.lhs) orelse return null;
            return placeField(check, node, base, access.name_token);
        },
        .deref => |operand| return placeThroughPointer(check, node, operand),
        .bracket => |view| return placeIndex(check, node, view),
        .err => return null,
        else => {
            const value = try check.checkExpr(node, null);
            return placeOfValue(check, node, value, null);
        },
    }
}

fn placeOfValue(
    check: *Check,
    node: Node.Index,
    value: Value,
    name: ?[]const u8,
) Allocator.Error!?Place {
    if (try check.valueOnly(node, value) == false) return null;
    if (value.stops()) return null;
    return .{
        .kind = .value,
        .ref = refOf(value),
        .type = check.typeOf(value),
        .node = node,
        .immutable = if (name == null) .temporary else .let_bound,
        .root_name = name orelse "this value",
        .root_node = node,
    };
}

fn placeThroughPointer(
    check: *Check,
    node: Node.Index,
    operand: Node.Index,
) Allocator.Error!?Place {
    const value = try check.checkValue(operand, null);
    const found = check.typeOf(value);
    if (found == .poison) return null;
    const pointer = try Expr.pointerAt(check, node, found, ".*", Expr.deref_help) orelse return null;
    return .{
        .kind = .address,
        .ref = refOf(value),
        .type = pointer.child,
        .node = node,
        .immutable = if (pointer.mutable) null else .{
            .read_only = .{ .form = .pointer, .child = pointer.child },
        },
        .root_name = "this pointer",
        .root_node = operand,
    };
}

fn placeField(
    check: *Check,
    node: Node.Index,
    base: Place,
    name_token: Token.Index,
) Allocator.Error!?Place {
    const comp = check.comp;
    const reached = try Expr.reachField(check, base.type, name_token) orelse return null;
    const row = switch (reached.member) {
        .field => |found| found,
        .method => unreachable,
        .length => return failNotAPlace(
            check,
            name_token,
            "an array's length is in its type, and a view keeps its own",
        ),
        .address => return failNotAPlace(
            check,
            name_token,
            "a view keeps the address it holds, so write through the view itself",
        ),
    };
    const row_type = comp.rowAt(row).type;

    const through = try placeThrough(check, base, reached.pointer) orelse return null;
    const field_pointer = try check.pointerTo(row_type, through.mutable());
    const place = try check.emit(node, .field_ptr, field_pointer, .{
        .field = .{ .base = through.ref, .row = row },
    });
    return through.reaching(node, place, row_type);
}

fn placeIndex(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Place {
    if (Aggregate.rangeIn(check, view) != null) {
        try Aggregate.checkBracketArgs(check, view);
        try check.fail(node, .{
            .code = .not_assignable,
            .message = "this makes a view, which is a value and not a place",
            .label = "nothing to write to or point at",
        });
        return null;
    }

    const indexed = try Aggregate.checkIndex(check, node, view) orelse return null;
    return elementPlace(check, indexed.elements, indexed.ref);
}

pub fn elementPlace(check: *Check, elements: Aggregate.Elements, index: Ref) Allocator.Error!?Place {
    assert(elements.child != .poison);
    assert(index != .none);

    const through = try elementsThrough(check, elements) orelse return null;
    if (settledAgainstBase(elements, index) == false) {
        const length = try baseLengthRef(check, elements, through);
        try emitCheck(check, elements.node, .bounds_check, index, length);
    }
    const element_pointer = try check.pointerTo(elements.child, through.mutable());
    const place = try check.emit(elements.node, .elem_ptr, element_pointer, .{
        .bin = .{ .lhs = through.ref, .rhs = index },
    });
    return through.reaching(elements.node, place, elements.child);
}

pub fn settledAgainstBase(elements: Aggregate.Elements, count: Ref) bool {
    return elements.len != null and refIsConstant(count);
}

pub fn baseLengthRef(check: *Check, elements: Aggregate.Elements, through: Place) Allocator.Error!Ref {
    const comp = check.comp;
    const count = elements.len orelse
        return check.emitOne(elements.node, .slice_len, .u64_type, through.ref);
    return .fromConstant(try comp.pool.int(comp.gpa, .u64_type, count));
}

pub fn emitCheck(
    check: *Check,
    node: Node.Index,
    tag: IR.Inst.Tag,
    lhs: Ref,
    rhs: Ref,
) Allocator.Error!void {
    assert(tag == .bounds_check or tag == .order_check);
    _ = try check.emit(node, tag, .void_type, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
}

pub fn refIsConstant(ref: Ref) bool {
    return ref.unwrap() == .constant;
}

pub fn elementsThrough(check: *Check, elements: Aggregate.Elements) Allocator.Error!?Place {
    if (elements.len != null) return placeThrough(check, elements.base, elements.pointer);

    var held = try placeValue(check, elements.base);
    if (elements.pointer != null) {
        held = try check.emitOne(elements.node, .load, elements.owner, held);
    }
    const base = elements.base.reaching(elements.base.node, held, elements.owner);
    return base.crossing(elements.mutable, .{ .form = .slice, .child = elements.child });
}

fn placeThrough(
    check: *Check,
    base: Place,
    pointer: ?Pool.Key.Pointer,
) Allocator.Error!?Place {
    const it = pointer orelse return placeAddress(check, base);
    const beyond = base.reaching(base.node, try placeValue(check, base), it.child);
    return beyond.crossing(it.mutable, .{ .form = .pointer, .child = it.child });
}

pub fn placeConstant(check: *const Check, place: Place) ?Pool.Index {
    if (place.kind != .value) return null;
    if (refIsConstant(place.ref) == false) return null;
    const held = place.ref.unwrap().constant;
    return switch (check.comp.pool.keyOf(held)) {
        .value_aggregate, .value_repeat => held,
        else => null,
    };
}

fn failNotAPlace(
    check: *Check,
    name_token: Token.Index,
    help: []const u8,
) Allocator.Error!?Place {
    try check.failToken(name_token, .{
        .code = .not_assignable,
        .message = try check.comp.fmt("'{s}' is a value and not a place", .{
            check.tree.tokenSlice(name_token),
        }),
        .label = "nothing to write to or point at",
        .help = help,
    });
    return null;
}

pub fn placeValue(check: *Check, place: Place) Allocator.Error!Ref {
    return switch (place.kind) {
        .value => place.ref,
        .address => try check.emitOne(place.node, .load, place.type, place.ref),
    };
}

/// Spills to a temporary, unobservable because only immutable values spill.
pub fn placeAddress(check: *Check, place: Place) Allocator.Error!?Place {
    if (place.kind == .address) return place;
    if (place.type == .poison) return null;
    assert(place.immutable != null);
    const slot = try check.emitSlot(place.node, .empty, place.type);
    try check.emitStore(place.node, slot, place.ref);
    return place.reaching(place.node, slot, place.type);
}

pub fn reportImmutable(
    check: *Check,
    node: Node.Index,
    place: Place,
    why: Place.Reason,
) Allocator.Error!void {
    const comp = check.comp;
    const report: Diagnostic.Report = switch (why) {
        .let_bound => .{
            .code = .not_assignable,
            .message = try comp.fmt("'{s}' was bound with 'let', so it cannot change", .{
                place.root_name,
            }),
            .label = "immutable",
            .help = "declare it 'var' if it needs to change",
            .notes = try check.noteHere(place.root_node, "bound here"),
        },
        .param_bound => .{
            .code = .not_assignable,
            .message = try comp.fmt(
                "'{s}' is a parameter, and a parameter is a copy that dies with the call",
                .{place.root_name},
            ),
            .label = "immutable",
            .help = "take '*var T' to write the caller's value, or copy it into a 'var' first",
        },
        .read_only => |crossed| .{
            .code = .write_through_pointer,
            .message = try comp.fmt("this writes through a '{s}', which is read-only", .{
                try comp.typeName(try crossedType(check, crossed, false)),
            }),
            .label = "read-only",
            .help = try comp.fmt("take '{s}' to write through it", .{
                try comp.typeName(try crossedType(check, crossed, true)),
            }),
        },
        .temporary => .{
            .code = .not_assignable,
            .message = "this value has no home, so there is nowhere to write",
            .label = "not a place",
        },
    };
    try check.fail(node, report);
}
