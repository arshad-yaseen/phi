const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Check = @import("../Check.zig");
const Compilation = @import("../Compilation.zig");
const IR = @import("../IR.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Resolve = @import("Resolve.zig");
const Expr = @import("Expr.zig");

const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;
const Value = Check.Value;
const refOf = Check.refOf;
const runtimeValue = Check.runtimeValue;

pub fn activeNarrow(check: *const Check, name: Name) ?Narrow {
    const narrows = check.comp.scratch.narrows.items;
    assert(narrows.len >= check.narrows_floor);
    var index = narrows.len;
    while (index > check.narrows_floor) {
        index -= 1;
        if (std.meta.eql(narrows[index].name, name)) return narrows[index];
    }
    return null;
}

pub fn narrowedName(check: *const Check, node: Node.Index) ?Name {
    if (check.tree.nodeTag(node) != .ident) return null;
    const text = check.mainTokenText(node);
    if (check.findLocalIndex(text)) |index| {
        if (check.localAt(index).kind == .var_slot) return null;
        return .{ .local = index };
    }
    const decl_index = Resolve.visibleDecl(check, text) orelse return null;
    if (check.comp.declAt(decl_index).kind != .let) return null;
    return .{ .decl = decl_index };
}

fn nameType(check: *const Check, name: Name) Pool.Index {
    return switch (name) {
        .local => |index| check.localAt(index).type,
        .decl => |index| check.comp.pool.typeOfValue(declConstant(check, index)),
    };
}

fn nameRef(check: *const Check, name: Name) Ref {
    return switch (name) {
        .local => |index| check.localAt(index).ref,
        .decl => |index| .fromConstant(declConstant(check, index)),
    };
}

fn declConstant(check: *const Check, decl_index: Decl.Index) Pool.Index {
    const decl = check.comp.declAt(decl_index);
    assert(decl.kind == .let);
    if (decl.state != .done) return .poison;
    return decl.answer.constant;
}

pub const Name = union(enum) { local: Check.Builder.Local.Index, decl: Decl.Index };

/// What a condition proved about one name, on one edge.
pub const Fact = struct { name: Name, type: Pool.Index, node: Node.Index };

/// A fact in force, with the value the name reads as while it holds.
pub const Narrow = struct { name: Name, type: Pool.Index, ref: Ref };

const Facts = struct {
    when_true: Compilation.Range,
    when_false: Compilation.Range,

    const nothing: Facts = .{ .when_true = .empty, .when_false = .empty };
};

pub fn gatherFacts(check: *Check, node: Node.Index) Allocator.Error!Facts {
    const comp = check.comp;
    switch (check.tree.viewOf(node)) {
        .is_expr => {
            // marked after the call, which can grow the list under a mark taken first
            const found = try factsOfIs(check, node) orelse return .nothing;
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
            try gatherWhenTrue(check, node);
            const len: u32 = @intCast(comp.scratch.facts.items.len - start);
            return .{ .when_true = .{ .start = start, .len = len }, .when_false = .empty };
        },
        else => return .nothing,
    }
}

fn gatherWhenTrue(check: *Check, node: Node.Index) Allocator.Error!void {
    switch (check.tree.viewOf(node)) {
        .is_expr => {
            const found = try factsOfIs(check, node) orelse return;
            try check.comp.scratch.facts.append(check.comp.gpa, found.when_true);
        },
        .binary => |it| {
            if (it.op != .bool_and) return;
            try gatherWhenTrue(check, it.lhs);
            try gatherWhenTrue(check, it.rhs);
        },
        else => {},
    }
}

fn factsOfIs(
    check: *Check,
    node: Node.Index,
) Allocator.Error!?struct { when_true: Fact, when_false: Fact } {
    const comp = check.comp;
    const view = check.tree.viewOf(node).is_expr;

    const name = narrowedName(check, view.operand) orelse return null;
    const found = if (activeNarrow(check, name)) |narrow| narrow.type else nameType(check, name);
    if (comp.pool.isUnion(found) == false) return null;

    const label = try Resolve.resolveType(check, view.type_expr);
    if (label == .poison) return null;
    if (comp.pool.subsumes(found, label) == false) return null;
    const rest = try comp.pool.unionWithout(comp.gpa, found, label) orelse return null;

    const holds: Fact = .{ .name = name, .type = label, .node = node };
    const others: Fact = .{ .name = name, .type = rest, .node = node };
    if (view.negated) return .{ .when_true = others, .when_false = holds };
    return .{ .when_true = holds, .when_false = others };
}

pub fn applyFacts(check: *Check, range: Compilation.Range) Allocator.Error!void {
    var at = range.start;
    // by index, because the run belongs to the builder rather than to this call
    while (at < range.end()) : (at += 1) try applyFact(check, check.comp.scratch.facts.items[at]);
}

pub fn applyFact(check: *Check, fact: Fact) Allocator.Error!void {
    const active = activeNarrow(check, fact.name);
    const source: Ref = if (active) |narrow| narrow.ref else nameRef(check, fact.name);
    const found: Pool.Index = if (active) |narrow| narrow.type else nameType(check, fact.name);
    assert(check.comp.pool.subsumes(found, fact.type));

    const narrowed: Ref = if (found == fact.type) source else switch (source.unwrap()) {
        .constant => |constant| .fromConstant(
            try check.comp.pool.narrowTo(check.comp.gpa, constant, fact.type),
        ),
        .inst => try check.emitOne(fact.node, .union_narrow, fact.type, source),
    };
    try check.comp.scratch.narrows.append(check.comp.gpa, .{
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

pub fn checkIs(check: *Check, node: Node.Index, view: AST.View.Is) Allocator.Error!Value {
    const comp = check.comp;
    const operand = try check.checkExpr(view.operand, null);
    const label = try Resolve.resolveType(check, view.type_expr);
    if (operand.stops()) return operand;
    if (label == .poison) return .poison;

    if (try Resolve.namedType(check, view.operand, operand)) |named| {
        if (named == .poison) return .poison;
        if (Resolve.unionBoundOfName(check, view.operand)) |bound| {
            if (try labelWithin(check, view.type_expr, label, bound) == false) return .poison;
        }
        return check.settledTruth(node, comp.pool.covers(label, named) != view.negated);
    }
    if (try check.valueOnly(view.operand, operand) == false) return .poison;

    const found = check.typeOf(operand);
    if (found == .poison) return .poison;
    if (comp.pool.isUnion(found) == false) {
        try Expr.failNotUnion(check, node, found, "'is' asks which member a union holds");
        return .poison;
    }
    if (try labelWithin(check, view.type_expr, label, found) == false) return .poison;

    if (operand == .constant) {
        const held = comp.pool.memberOfValue(operand.constant);
        return check.settledTruth(node, comp.pool.covers(label, held) != view.negated);
    }

    if (check.builder == null) return check.needRuntime(node, "an 'is' test");
    assert(operand == .runtime);
    const bools = try check.boolType(node);
    const tested = try check.emit(node, .union_is, bools, .{
        .probe = .{ .operand = refOf(operand), .member = label },
    });
    if (view.negated) return check.emitOneValue(node, .not, bools, tested);
    return runtimeValue(tested, bools);
}

pub fn labelWithin(
    check: *Check,
    label_node: Node.Index,
    label: Pool.Index,
    union_type: Pool.Index,
) Allocator.Error!bool {
    const pool = &check.comp.pool;
    if (pool.subsumes(union_type, label)) return true;

    var stray = label;
    if (pool.isUnion(label)) {
        for (pool.unionMembers(label)) |member| {
            if (pool.unionHas(union_type, member)) continue;
            stray = member;
            break;
        }
    }
    try Expr.failNotMember(check, label_node, stray, union_type);
    return false;
}
