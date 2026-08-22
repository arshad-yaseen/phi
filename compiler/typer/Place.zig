const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const Diagnostic = @import("../Diagnostic.zig");
const IR = @import("../IR.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Narrow = @import("Narrow.zig");
const Expr = @import("Expr.zig");
const Aggregate = @import("Aggregate.zig");

const Node = AST.Node;
const Ref = IR.Ref;
const Value = Typer.Value;
const refOf = Typer.refOf;
const runtimeValue = Typer.runtimeValue;

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

pub fn checkAddressOf(typer: *Typer, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = typer.comp;
    if (typer.builder == null) return typer.needRuntime(node, "taking an address");

    const place = try checkPlace(typer, view.operand) orelse return .poison;
    if (typer.typeCanHold(place.type) == false) {
        return typer.refuseToken(view.op_token, .{
            .code = .type_mismatch,
            .message = try comp.fmt("'&' needs a value with a type, and this is {s}", .{
                try comp.typeName(place.type),
            }),
            .label = "nothing to point at",
            .help = "give the value a type first, as in 'let n: i64 = 10'",
        });
    }
    const addressed = try placeAddress(typer, place) orelse return .poison;
    return runtimeValue(addressed.ref, try typer.pointerTo(addressed.type, addressed.mutable()));
}

pub fn checkDeref(typer: *Typer, node: Node.Index) Allocator.Error!Value {
    const place = try checkPlace(typer, node) orelse return .poison;
    return runtimeValue(try placeValue(typer, place), place.type);
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

pub fn crossedType(typer: *Typer, crossed: Place.Crossed, writable: bool) Allocator.Error!Pool.Index {
    return switch (crossed.form) {
        .pointer => typer.pointerTo(crossed.child, writable),
        .slice => typer.sliceOf(crossed.child, writable),
    };
}

fn localPlace(
    typer: *const Typer,
    node: Node.Index,
    index: Typer.Builder.Local.Index,
    text: []const u8,
) Place {
    const local = typer.localAt(index);
    const narrow = Narrow.activeNarrow(typer, .{ .local = index });
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

pub fn checkPlace(typer: *Typer, node: Node.Index) Allocator.Error!?Place {
    if (typer.builder == null) {
        const value = try typer.checkExpr(node, null);
        return placeOfValue(typer, node, value, null);
    }

    switch (typer.tree.viewOf(node)) {
        .ident => {
            const text = typer.mainTokenText(node);
            if (Module.isDiscard(text)) {
                try typer.failDiscard(node);
                return null;
            }
            if (typer.findLocalIndex(text)) |index| {
                if (typer.localAt(index).type == .poison) return null;
                return localPlace(typer, node, index, text);
            }
            const value = try typer.checkExpr(node, null);
            return placeOfValue(typer, node, value, text);
        },
        .field_access => |access| {
            const base = try checkPlace(typer, access.lhs) orelse return null;
            return placeField(typer, node, base, access.name_token);
        },
        .deref => |operand| return placeThroughPointer(typer, node, operand),
        .bracket => |view| return placeIndex(typer, node, view),
        .err => return null,
        else => {
            const value = try typer.checkExpr(node, null);
            return placeOfValue(typer, node, value, null);
        },
    }
}

fn placeOfValue(
    typer: *Typer,
    node: Node.Index,
    value: Value,
    name: ?[]const u8,
) Allocator.Error!?Place {
    if (try typer.valueOnly(node, value) == false) return null;
    if (value.stops()) return null;
    return .{
        .kind = .value,
        .ref = refOf(value),
        .type = typer.typeOf(value),
        .node = node,
        .immutable = if (name == null) .temporary else .let_bound,
        .root_name = name orelse "this value",
        .root_node = node,
    };
}

fn placeThroughPointer(
    typer: *Typer,
    node: Node.Index,
    operand: Node.Index,
) Allocator.Error!?Place {
    const value = try typer.checkValue(operand, null);
    const found = typer.typeOf(value);
    if (found == .poison) return null;
    const pointer = try Expr.pointerAt(typer, node, found, ".*", Expr.deref_help) orelse return null;
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
    typer: *Typer,
    node: Node.Index,
    base: Place,
    name_token: Token.Index,
) Allocator.Error!?Place {
    const comp = typer.comp;
    const reached = try Expr.reachField(typer, base.type, name_token) orelse return null;
    const row = switch (reached.member) {
        .field => |found| found,
        .method => unreachable,
        .length => return failNotAPlace(
            typer,
            name_token,
            "an array's length is in its type, and a view keeps its own",
        ),
        .address => return failNotAPlace(
            typer,
            name_token,
            "a view keeps the address it holds, so write through the view itself",
        ),
    };
    const row_type = comp.rowAt(row).type;

    const through = try placeThrough(typer, base, reached.pointer) orelse return null;
    const field_pointer = try typer.pointerTo(row_type, through.mutable());
    const place = try typer.emit(node, .field_ptr, field_pointer, .{
        .field = .{ .base = through.ref, .row = row },
    });
    return through.reaching(node, place, row_type);
}

fn placeIndex(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Place {
    if (Aggregate.rangeIn(typer, view) != null) {
        try Aggregate.checkBracketArgs(typer, view);
        try typer.fail(node, .{
            .code = .not_assignable,
            .message = "this makes a view, which is a value and not a place",
            .label = "nothing to write to or point at",
        });
        return null;
    }

    const indexed = try Aggregate.checkIndex(typer, node, view) orelse return null;
    return elementPlace(typer, indexed.elements, indexed.ref);
}

pub fn elementPlace(typer: *Typer, elements: Aggregate.Elements, index: Ref) Allocator.Error!?Place {
    assert(elements.child != .poison);
    assert(index != .none);

    const through = try elementsThrough(typer, elements) orelse return null;
    if (settledAgainstBase(elements, index) == false) {
        const length = try baseLengthRef(typer, elements, through);
        try emitCheck(typer, elements.node, .bounds_check, index, length);
    }
    const element_pointer = try typer.pointerTo(elements.child, through.mutable());
    const place = try typer.emit(elements.node, .elem_ptr, element_pointer, .{
        .bin = .{ .lhs = through.ref, .rhs = index },
    });
    return through.reaching(elements.node, place, elements.child);
}

pub fn settledAgainstBase(elements: Aggregate.Elements, count: Ref) bool {
    return elements.len != null and refIsConstant(count);
}

pub fn baseLengthRef(typer: *Typer, elements: Aggregate.Elements, through: Place) Allocator.Error!Ref {
    const comp = typer.comp;
    const count = elements.len orelse
        return typer.emitOne(elements.node, .slice_len, .u64_type, through.ref);
    return .fromConstant(try comp.pool.int(comp.gpa, .u64_type, count));
}

pub fn emitCheck(
    typer: *Typer,
    node: Node.Index,
    tag: IR.Inst.Tag,
    lhs: Ref,
    rhs: Ref,
) Allocator.Error!void {
    assert(tag == .bounds_check or tag == .order_check);
    _ = try typer.emit(node, tag, .void_type, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
}

pub fn refIsConstant(ref: Ref) bool {
    return ref.unwrap() == .constant;
}

pub fn elementsThrough(typer: *Typer, elements: Aggregate.Elements) Allocator.Error!?Place {
    if (elements.len != null) return placeThrough(typer, elements.base, elements.pointer);

    var held = try placeValue(typer, elements.base);
    if (elements.pointer != null) {
        held = try typer.emitOne(elements.node, .load, elements.owner, held);
    }
    const base = elements.base.reaching(elements.base.node, held, elements.owner);
    return base.crossing(elements.mutable, .{ .form = .slice, .child = elements.child });
}

fn placeThrough(
    typer: *Typer,
    base: Place,
    pointer: ?Pool.Key.Pointer,
) Allocator.Error!?Place {
    const it = pointer orelse return placeAddress(typer, base);
    const beyond = base.reaching(base.node, try placeValue(typer, base), it.child);
    return beyond.crossing(it.mutable, .{ .form = .pointer, .child = it.child });
}

pub fn placeConstant(typer: *const Typer, place: Place) ?Pool.Index {
    if (place.kind != .value) return null;
    if (refIsConstant(place.ref) == false) return null;
    const held = place.ref.unwrap().constant;
    return switch (typer.comp.pool.keyOf(held)) {
        .value_aggregate, .value_repeat => held,
        else => null,
    };
}

fn failNotAPlace(
    typer: *Typer,
    name_token: Token.Index,
    help: []const u8,
) Allocator.Error!?Place {
    try typer.failToken(name_token, .{
        .code = .not_assignable,
        .message = try typer.comp.fmt("'{s}' is a value and not a place", .{
            typer.tree.tokenSlice(name_token),
        }),
        .label = "nothing to write to or point at",
        .help = help,
    });
    return null;
}

pub fn placeValue(typer: *Typer, place: Place) Allocator.Error!Ref {
    return switch (place.kind) {
        .value => place.ref,
        .address => try typer.emitOne(place.node, .load, place.type, place.ref),
    };
}

/// Spills to a temporary, unobservable because only immutable values spill.
pub fn placeAddress(typer: *Typer, place: Place) Allocator.Error!?Place {
    if (place.kind == .address) return place;
    if (place.type == .poison) return null;
    assert(place.immutable != null);
    const slot = try typer.emitSlot(place.node, .empty, place.type);
    try typer.emitStore(place.node, slot, place.ref);
    return place.reaching(place.node, slot, place.type);
}

pub fn reportImmutable(
    typer: *Typer,
    node: Node.Index,
    place: Place,
    why: Place.Reason,
) Allocator.Error!void {
    const comp = typer.comp;
    const report: Diagnostic.Report = switch (why) {
        .let_bound => .{
            .code = .not_assignable,
            .message = try comp.fmt("'{s}' was bound with 'let', so it cannot change", .{
                place.root_name,
            }),
            .label = "immutable",
            .help = "declare it 'var' if it needs to change",
            .notes = try typer.noteHere(place.root_node, "bound here"),
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
                try comp.typeName(try crossedType(typer, crossed, false)),
            }),
            .label = "read-only",
            .help = try comp.fmt("take '{s}' to write through it", .{
                try comp.typeName(try crossedType(typer, crossed, true)),
            }),
        },
        .temporary => .{
            .code = .not_assignable,
            .message = "this value has no home, so there is nowhere to write",
            .label = "not a place",
        },
    };
    try typer.fail(node, report);
}
