const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const Compilation = @import("../Compilation.zig");
const IR = @import("../IR.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Resolve = @import("Resolve.zig");
const Expr = @import("Expr.zig");

const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;
const Value = Typer.Value;
const refOf = Typer.refOf;
const runtimeValue = Typer.runtimeValue;

pub fn activeNarrow(typer: *const Typer, name: Name) ?Narrow {
    const narrows = typer.comp.scratch.narrows.items;
    assert(narrows.len >= typer.narrows_floor);
    var index = narrows.len;
    while (index > typer.narrows_floor) {
        index -= 1;
        if (std.meta.eql(narrows[index].name, name)) return narrows[index];
    }
    return null;
}

pub fn narrowedName(typer: *const Typer, node: Node.Index) ?Name {
    if (typer.tree.nodeTag(node) != .ident) return null;
    const text = typer.mainTokenText(node);
    if (typer.findLocalIndex(text)) |index| {
        if (typer.localAt(index).kind == .var_slot) return null;
        return .{ .local = index };
    }
    const decl_index = Resolve.visibleDecl(typer, text) orelse return null;
    if (typer.comp.declAt(decl_index).kind != .let) return null;
    return .{ .decl = decl_index };
}

fn nameType(typer: *const Typer, name: Name) Pool.Index {
    return switch (name) {
        .local => |index| typer.localAt(index).type,
        .decl => |index| typer.comp.pool.typeOfValue(declConstant(typer, index)),
    };
}

fn nameRef(typer: *const Typer, name: Name) Ref {
    return switch (name) {
        .local => |index| typer.localAt(index).ref,
        .decl => |index| .fromConstant(declConstant(typer, index)),
    };
}

fn declConstant(typer: *const Typer, decl_index: Decl.Index) Pool.Index {
    const decl = typer.comp.declAt(decl_index);
    assert(decl.kind == .let);
    if (decl.state != .done) return .poison;
    return decl.answer.constant;
}

pub const Name = union(enum) { local: Typer.Builder.Local.Index, decl: Decl.Index };

/// What a condition proved about one name, on one edge.
pub const Fact = struct { name: Name, type: Pool.Index, node: Node.Index };

/// A fact in force, with the value the name reads as while it holds.
pub const Narrow = struct { name: Name, type: Pool.Index, ref: Ref };

const Facts = struct {
    when_true: Compilation.Range,
    when_false: Compilation.Range,

    const nothing: Facts = .{ .when_true = .empty, .when_false = .empty };
};

pub fn gatherFacts(typer: *Typer, node: Node.Index) Allocator.Error!Facts {
    const comp = typer.comp;
    switch (typer.tree.viewOf(node)) {
        .is_expr => {
            // marked after the call, which can grow the list under a mark taken first
            const found = try factsOfIs(typer, node) orelse return .nothing;
            const start: u32 = @intCast(comp.scratch.facts.items.len);
            try comp.scratch.facts.append(comp.gpa, found.when_true);
            try comp.scratch.facts.append(comp.gpa, found.when_false);
            return .{
                .when_true = .{ .start = start, .len = 1 },
                .when_false = .{ .start = start + 1, .len = 1 },
            };
        },
        .binary => |it| {
            if (it.op != .bool_and) return .nothing;
            const start: u32 = @intCast(comp.scratch.facts.items.len);
            try gatherWhenTrue(typer, node);
            const len: u32 = @intCast(comp.scratch.facts.items.len - start);
            return .{ .when_true = .{ .start = start, .len = len }, .when_false = .empty };
        },
        else => return .nothing,
    }
}

fn gatherWhenTrue(typer: *Typer, node: Node.Index) Allocator.Error!void {
    switch (typer.tree.viewOf(node)) {
        .is_expr => {
            const found = try factsOfIs(typer, node) orelse return;
            try typer.comp.scratch.facts.append(typer.comp.gpa, found.when_true);
        },
        .binary => |it| {
            if (it.op != .bool_and) return;
            try gatherWhenTrue(typer, it.lhs);
            try gatherWhenTrue(typer, it.rhs);
        },
        else => {},
    }
}

fn factsOfIs(
    typer: *Typer,
    node: Node.Index,
) Allocator.Error!?struct { when_true: Fact, when_false: Fact } {
    const comp = typer.comp;
    const view = typer.tree.viewOf(node).is_expr;

    const name = narrowedName(typer, view.operand) orelse return null;
    const found = if (activeNarrow(typer, name)) |narrow| narrow.type else nameType(typer, name);
    if (comp.pool.isUnion(found) == false) return null;

    const label = try Resolve.resolveType(typer, view.type_expr);
    if (label == .poison) return null;
    if (comp.pool.subsumes(found, label) == false) return null;
    const rest = try comp.pool.unionWithout(comp.gpa, found, label) orelse return null;

    const holds: Fact = .{ .name = name, .type = label, .node = node };
    const others: Fact = .{ .name = name, .type = rest, .node = node };
    if (view.negated) return .{ .when_true = others, .when_false = holds };
    return .{ .when_true = holds, .when_false = others };
}

pub fn applyFacts(typer: *Typer, range: Compilation.Range) Allocator.Error!void {
    var at = range.start;
    // by index, because the run belongs to the builder rather than to this call
    while (at < range.end()) : (at += 1) try applyFact(typer, typer.comp.scratch.facts.items[at]);
}

pub fn applyFact(typer: *Typer, fact: Fact) Allocator.Error!void {
    const active = activeNarrow(typer, fact.name);
    const source: Ref = if (active) |narrow| narrow.ref else nameRef(typer, fact.name);
    const found: Pool.Index = if (active) |narrow| narrow.type else nameType(typer, fact.name);
    assert(typer.comp.pool.subsumes(found, fact.type));

    const narrowed: Ref = if (found == fact.type) source else switch (source.unwrap()) {
        .constant => |constant| .fromConstant(
            try typer.comp.pool.narrowTo(typer.comp.gpa, constant, fact.type),
        ),
        .inst => try typer.emitOne(fact.node, .union_narrow, fact.type, source),
    };
    try typer.comp.scratch.narrows.append(typer.comp.gpa, .{
        .name = fact.name,
        .type = fact.type,
        .ref = narrowed,
    });
}

pub fn valueOfRef(ref: Ref, type_index: Pool.Index) Value {
    return switch (ref.unwrap()) {
        .constant => |constant| .{ .constant = constant },
        .inst => runtimeValue(ref, type_index),
    };
}

pub fn checkIs(typer: *Typer, node: Node.Index, view: AST.View.Is) Allocator.Error!Value {
    const comp = typer.comp;
    const operand = try typer.checkExpr(view.operand, null);
    const label = try Resolve.resolveType(typer, view.type_expr);
    if (operand.stops()) return operand;
    if (label == .poison) return .poison;

    if (try Resolve.namedType(typer, view.operand, operand)) |named| {
        if (named == .poison) return .poison;
        if (Resolve.unionBoundOfName(typer, view.operand)) |bound| {
            if (try labelWithin(typer, view.type_expr, label, bound) == false) return .poison;
        }
        return typer.settledTruth(node, comp.pool.covers(label, named) != view.negated);
    }
    if (try typer.valueOnly(view.operand, operand) == false) return .poison;

    const found = typer.typeOf(operand);
    if (found == .poison) return .poison;
    if (comp.pool.isUnion(found) == false) {
        try Expr.failNotUnion(typer, node, found, "'is' asks which member a union holds");
        return .poison;
    }
    if (try labelWithin(typer, view.type_expr, label, found) == false) return .poison;

    if (operand == .constant) {
        const held = comp.pool.memberOfValue(operand.constant);
        return typer.settledTruth(node, comp.pool.covers(label, held) != view.negated);
    }

    if (typer.builder == null) return typer.needRuntime(node, "an 'is' test");
    assert(operand == .runtime);
    const bools = try typer.boolType(node);
    const tested = try typer.emit(node, .union_is, bools, .{
        .probe = .{ .operand = refOf(operand), .member = label },
    });
    if (view.negated) return typer.emitOneValue(node, .not, bools, tested);
    return runtimeValue(tested, bools);
}

pub fn labelWithin(
    typer: *Typer,
    label_node: Node.Index,
    label: Pool.Index,
    union_type: Pool.Index,
) Allocator.Error!bool {
    const pool = &typer.comp.pool;
    if (pool.subsumes(union_type, label)) return true;

    var stray = label;
    if (pool.isUnion(label)) {
        for (pool.unionMembers(label)) |member| {
            if (pool.unionHas(union_type, member)) continue;
            stray = member;
            break;
        }
    }
    try Expr.failNotMember(typer, label_node, stray, union_type);
    return false;
}
