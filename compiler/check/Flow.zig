const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Check = @import("../Check.zig");
const Compilation = @import("../Compilation.zig");
const IR = @import("../IR.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Resolve = @import("Resolve.zig");
const Narrowing = @import("Narrowing.zig");
const Expr = @import("Expr.zig");
const Aggregate = @import("Aggregate.zig");

const Node = AST.Node;
const Ref = IR.Ref;
const Value = Check.Value;
const broken_ref = Check.broken_ref;
const refOf = Check.refOf;
const runtimeValue = Check.runtimeValue;
const wantsValue = Check.wantsValue;
const quotedList = Check.quotedList;

pub fn checkIf(
    check: *Check,
    node: Node.Index,
    view: AST.View.If,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;

    const wants = wantsValue(hint);
    if (wants and view.else_node == .none) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this 'if' has no 'else', so one path through it produces nothing",
            .label = "needs an 'else'",
            .help = "an 'if' used as a value says what it is on every path",
        });
    }

    const cond = try checkCondition(check, view.cond);
    if (cond == broken_ref) return .poison;

    const facts_mark: u32 = @intCast(comp.scratch.facts.items.len);
    defer comp.scratch.facts.shrinkRetainingCapacity(facts_mark);
    const facts = try Narrowing.gatherFacts(check, view.cond);

    if (conditionTruth(check, cond)) |truth| {
        const taken = if (truth) view.then_block.toOptional() else view.else_node;
        const proved = if (truth) facts.when_true else facts.when_false;
        const value = try checkChosen(check, taken, proved, hint);

        if (value != .diverged) {
            try Narrowing.applyFacts(check, proved);
            return value;
        }
        if (view.else_node != .none) return value;

        assert(truth);
        try fallsPast(check);
        try Narrowing.applyFacts(check, facts.when_false);
        return .void_value;
    }

    const builder = check.body();
    const carries = wants and view.else_node != .none;
    var join = try Join.open(check, "if", node, carries, hint, node.toOptional());

    const then_block = try check.newBlock();
    const else_block = try check.newBlock();
    const join_block = try check.newBlock();

    try check.reopenDead();
    const entry_reachable = builder.reachable;
    check.endBlock(.{ .branch = .{
        .cond = cond,
        .then_block = then_block,
        .else_block = else_block,
    } });

    const narrows_mark = comp.scratch.narrows.items.len;

    check.startBlock(then_block);
    builder.reachable = entry_reachable;
    try Narrowing.applyFacts(check, facts.when_true);
    const then_value = try check.checkExpr(view.then_block, hint);
    comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);
    try join.take(check, then_value, view.then_block);
    var join_reachable = check.jumpTo(join_block);

    check.startBlock(else_block);
    builder.reachable = entry_reachable;
    var else_value: Value = .diverged;
    if (view.else_node.unwrap()) |else_node| {
        try Narrowing.applyFacts(check, facts.when_false);
        else_value = try check.checkExpr(else_node, hint);
        comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);
        try join.take(check, else_value, else_node);
        if (check.jumpTo(join_block)) join_reachable = true;
    } else {
        if (entry_reachable) join_reachable = true;
        check.endBlock(.{ .jump = join_block });
    }

    check.startBlock(join_block);
    builder.reachable = join_reachable;

    if (then_value == .diverged and (view.else_node == .none or else_value != .diverged)) {
        try Narrowing.applyFacts(check, facts.when_false);
    }
    if (then_value != .diverged and view.else_node != .none and else_value == .diverged) {
        try Narrowing.applyFacts(check, facts.when_true);
    }
    return join.close(check, then_value == .diverged and else_value == .diverged);
}

pub const Join = struct {
    what: []const u8,
    node: Node.Index,
    /// `.none` for a statement, where the arms produce nothing.
    slot: Ref,
    result_type: Pool.Index,
    carries: bool,
    settled: bool,
    names_type: Node.OptionalIndex,

    fn open(
        check: *Check,
        what: []const u8,
        node: Node.Index,
        carries: bool,
        hint: ?Pool.Index,
        names_type: Node.OptionalIndex,
    ) Allocator.Error!Join {
        return .{
            .what = what,
            .node = node,
            .slot = if (carries) try check.emitSlot(node, .empty, hint orelse .poison) else .none,
            .result_type = hint orelse .poison,
            .carries = carries,
            .settled = hint != null,
            .names_type = names_type,
        };
    }

    fn armHint(join: Join) ?Pool.Index {
        if (join.carries == false) return .void_type;
        return if (join.settled) join.result_type else null;
    }

    fn take(join: *Join, check: *Check, value: Value, at: Node.Index) Allocator.Error!void {
        if (join.carries == false) return;
        if (value == .diverged) return;
        if (try check.valueOnly(at, value) == false) return;

        if (join.settled == false) {
            const found = check.typeOf(value);
            if (value == .constant and Pool.isUntyped(found)) {
                return check.emitStore(at, join.slot, refOf(value));
            }
            const blamed = join.names_type.unwrap() orelse at;
            join.result_type = try settleType(check, blamed, found, join.what);
            join.settled = true;
        }
        const met = try check.coerce(value, join.result_type, at);
        try check.emitStore(at, join.slot, refOf(met));
    }

    fn close(join: Join, check: *Check, diverged: bool) Allocator.Error!Value {
        if (join.carries == false) return .void_value;
        try setSlotType(check, join.slot, if (join.settled) join.result_type else .u8_type);
        try join.settleWaiting(check);

        if (diverged) return .diverged;
        if (join.result_type == .poison) return .poison;
        return check.emitOneValue(join.node, .load, join.result_type, join.slot);
    }

    fn settleWaiting(join: Join, check: *Check) Allocator.Error!void {
        const builder = check.body();
        const pool = &check.comp.pool;
        const tags = builder.insts.items(.tag);
        const data = builder.insts.items(.data);
        const nodes = builder.insts.items(.node);

        // the slot was emitted first, so its stores all follow it
        var at = join.slot.unwrap().inst.int() + 1;
        while (at < builder.insts.len) : (at += 1) {
            if (tags[at] != .store) continue;
            if (data[at].bin.lhs != join.slot) continue;
            const constant = switch (data[at].bin.rhs.unwrap()) {
                .constant => |constant| constant,
                .inst => continue,
            };
            if (Pool.isUntyped(pool.typeOfValue(constant)) == false) continue;

            if (join.settled == false) {
                const blamed = join.names_type.unwrap() orelse nodes[at];
                _ = try settleType(check, blamed, pool.typeOfValue(constant), join.what);
                return;
            }
            const met = try check.fitValue(constant, join.result_type, nodes[at]);
            data[at].bin.rhs = refOf(met);
        }
    }
};

fn checkChosen(
    check: *Check,
    arm: Node.OptionalIndex,
    proved: Compilation.Range,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const narrows_mark = comp.scratch.narrows.items.len;
    defer comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);

    try Narrowing.applyFacts(check, proved);
    const taken = arm.unwrap() orelse return .void_value;

    const value = try check.checkExpr(taken, hint);
    if (wantsValue(hint)) return value;
    try check.expectNothing(taken, value);
    return if (value == .diverged) .diverged else .void_value;
}

fn fallsPast(check: *Check) Allocator.Error!void {
    const builder = check.body();
    const reached = builder.reachable;
    check.startBlock(try check.newBlock());
    builder.reachable = reached;
}

fn settleType(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
) Allocator.Error!Pool.Index {
    const comp = check.comp;
    if (found == .poison) return .poison;
    if (check.typeCanHold(found)) return found;

    if (found == .void_type) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = try comp.fmt("this produces nothing, and the '{s}' needs a value", .{what}),
            .label = "no value here",
        });
    } else {
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = try comp.fmt("nothing says what type this '{s}' is", .{what}),
            .label = "no type in sight",
            .help = try comp.fmt("annotate what it feeds, as in 'let n: i64 = {s} ...'", .{what}),
        });
    }
    return .poison;
}

fn loopLabel(check: *Check, token: ?Token.Index) Allocator.Error!Pool.String {
    const comp = check.comp;
    const named = token orelse return .empty;

    const text = check.tree.tokenSlice(named);
    const label = try comp.pool.string(comp.gpa, text);
    for (check.body().loops.items) |other| {
        if (other.label != label) continue;
        try check.failToken(named, .{
            .code = .shadows,
            .message = try comp.fmt("':{s}' already names an enclosing loop", .{text}),
            .label = "shadows it",
            .notes = try check.noteHere(other.node, "first labeled here"),
        });
        break;
    }
    return label;
}

pub fn checkLoop(
    check: *Check,
    node: Node.Index,
    view: AST.View.Loop,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const builder = check.body();
    assert(check.tree.nodeTag(node) == .loop_expr);

    if (check.tree.nodeTag(view.body) != .block) return .poison;

    try check.reopenDead();

    const carries = wantsValue(hint);
    const else_missing = carries and view.head.ends() and view.else_node == .none;
    if (else_missing) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this loop has no 'else', so it has no value when it ends on its own",
            .label = "needs an 'else'",
            .help = "a loop used as a value says what it is when it ends on its own",
        });
    }

    var join = try Join.open(check, "loop", node, carries, hint, .none);
    const label = try loopLabel(check, view.label);

    const counting: ?AST.View.LoopRange = switch (view.head) {
        .range => |it| it,
        .forever, .cond => null,
    };
    const counter: ?Counter = if (counting) |it| try startCounter(check, it.name, it.over) else null;
    try check.reopenDead();

    const header = try check.newBlock();
    const body_block = try check.newBlock();
    const exit = try check.newBlock();
    const else_target: IR.Block.Index = if (view.else_node != .none) try check.newBlock() else exit;
    // the increment gets its own block so `continue` hits it before the test
    const latch: IR.Block.Index = if (counter != null) try check.newBlock() else header;

    check.endBlock(.{ .jump = header });
    check.startBlock(header);
    const holds: ?Ref = switch (view.head) {
        .forever => null,
        .cond => |cond_node| asked: {
            const cond = try checkCondition(check, cond_node);
            try check.reopenDead();
            break :asked cond;
        },
        .range => try counterBelowEnd(check, counter),
    };
    const runs = builder.reachable;
    if (holds) |cond| {
        check.endBlock(.{ .branch = .{
            .cond = cond,
            .then_block = body_block,
            .else_block = else_target,
        } });
    } else {
        check.endBlock(.{ .jump = body_block });
    }

    try builder.loops.append(comp.gpa, .{
        .label = label,
        .node = node,
        .header = latch,
        .exit = exit,
        .scope_depth = @intCast(builder.scopes.items.len),
        .join = join,
        .broke_reachable = false,
    });

    check.startBlock(body_block);
    builder.reachable = runs;
    if (counting) |it| try bindCounter(check, it.name, counter);
    _ = try check.checkBlockValue(view.body, .void_type);
    if (counting != null) check.popScope();
    if (check.blockOpen()) check.endBlock(.{ .jump = latch });

    if (counter) |it| {
        check.startBlock(latch);
        try countOn(check, it);
        check.endBlock(.{ .jump = header });
    }

    const finished = builder.loops.getLast();
    builder.loops.shrinkRetainingCapacity(builder.loops.items.len - 1);
    join = finished.join;

    var else_flows = false;
    if (view.else_node.unwrap()) |else_node| {
        check.startBlock(else_target);
        builder.reachable = runs and view.head.ends();
        if (view.head.ends() == false) {
            try check.fail(else_node, .{
                .code = .unreachable_code,
                .message = "this 'else' never runs, because a loop with no " ++
                    "condition never ends on its own",
                .label = "never runs",
            });
        }
        const else_value = try check.checkExpr(else_node, join.armHint());
        try join.take(check, else_value, else_node);
        else_flows = check.jumpTo(exit);
    }

    check.startBlock(exit);
    const ends_here = if (view.else_node == .none) runs else else_flows;
    const exit_reachable = finished.broke_reachable or (view.head.ends() and ends_here);
    builder.reachable = exit_reachable;

    const value = try join.close(check, exit_reachable == false);
    return if (else_missing) .poison else value;
}

const Counter = struct {
    slot: Ref,
    /// Read once, before the first pass.
    end: Ref,
    type: Pool.Index,
    node: Node.Index,
};

fn startCounter(check: *Check, name: Node.Index, over: Node.Index) Allocator.Error!?Counter {
    const comp = check.comp;
    if (check.tree.nodeTag(over) != .range_expr) return null;

    const range = check.tree.viewOf(over).range_expr;
    const end_node = range.end.unwrap() orelse return null;

    const first = try Aggregate.checkRangeEnd(check, range.start) orelse return null;
    const last = try Aggregate.checkRangeEnd(check, end_node) orelse return null;
    const ends = try Aggregate.settleEnds(
        check,
        over,
        .{ .value = first, .node = range.start },
        .{ .value = last, .node = end_node },
    ) orelse return null;
    if (try Aggregate.rangeRunsBackwards(check, over, ends.start, ends.end)) return null;

    const text = check.mainTokenText(name);
    const named: Pool.String = if (Module.isDiscard(text))
        .empty
    else
        try comp.pool.string(comp.gpa, text);
    const slot = try check.emitSlot(over, named, ends.type);
    try check.emitStore(over, slot, refOf(ends.start));
    return .{ .slot = slot, .end = refOf(ends.end), .type = ends.type, .node = over };
}

fn counterBelowEnd(check: *Check, counter: ?Counter) Allocator.Error!Ref {
    const it = counter orelse return broken_ref;
    const current = try check.emitOne(it.node, .load, it.type, it.slot);
    return check.emit(it.node, .cmp_lt, .void_type, .{ .bin = .{ .lhs = current, .rhs = it.end } });
}

fn bindCounter(check: *Check, name: Node.Index, counter: ?Counter) Allocator.Error!void {
    try check.pushScope();

    const text = check.mainTokenText(name);
    if (Module.isDiscard(text)) return check.failDiscard(name);
    const named = try check.comp.pool.string(check.comp.gpa, text);

    const it = counter orelse return check.declarePoisoned(named, name);
    const current = try check.emitOne(name, .load, it.type, it.slot);
    try check.declareLocal(named, name, .let, current, it.type);
}

fn countOn(check: *Check, counter: Counter) Allocator.Error!void {
    const comp = check.comp;
    const current = try check.emitOne(counter.node, .load, counter.type, counter.slot);
    const one = try comp.pool.int(comp.gpa, counter.type, 1);
    const next = try check.emit(counter.node, .add, counter.type, .{
        .bin = .{ .lhs = current, .rhs = .fromConstant(one) },
    });
    try check.emitStore(counter.node, counter.slot, next);
}

fn setSlotType(check: *Check, slot: Ref, value_type: Pool.Index) Allocator.Error!void {
    const builder = check.body();
    const index = slot.unwrap().inst.int();
    assert(builder.insts.items(.tag)[index] == .local);
    builder.insts.items(.type)[index] = try check.pointerTo(value_type, true);
}

const Subject = struct {
    /// The union the arms must cover, or null for an open set of types.
    set: ?Pool.Index,
    /// What the scrutinee is settled as, or null where only running tells.
    held: ?Pool.Index,
    ref: Ref,
    narrows: ?Narrows,

    const Narrows = struct { name: Narrowing.Name, set: Pool.Index };
};

fn matchSubject(check: *Check, scrutinee: Node.Index, value: Value) Allocator.Error!?Subject {
    const comp = check.comp;
    if (try Resolve.namedType(check, scrutinee, value)) |named| {
        if (named == .poison) return null;
        return .{
            .set = Resolve.unionBoundOfName(check, scrutinee),
            .held = named,
            .ref = broken_ref,
            .narrows = null,
        };
    }

    if (try check.valueOnly(scrutinee, value) == false) return null;
    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (comp.pool.isUnion(found) == false) {
        try Expr.failNotUnion(check, scrutinee, found, "'match' asks which member a union holds");
        return null;
    }

    const narrows: ?Subject.Narrows = if (Narrowing.narrowedName(check, scrutinee)) |name|
        .{ .name = name, .set = found }
    else
        null;
    return .{
        .set = found,
        .held = if (value == .constant) comp.pool.memberOfValue(value.constant) else null,
        .ref = refOf(value),
        .narrows = narrows,
    };
}

pub fn checkMatch(
    check: *Check,
    node: Node.Index,
    view: AST.View.Match,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .match_expr);

    const scrutinee = try check.checkExpr(view.scrutinee, null);

    const subject = try matchSubject(check, view.scrutinee, scrutinee) orelse {
        for (view.arms) |arm_node| {
            if (check.tree.nodeTag(arm_node) != .match_arm) continue;
            _ = try check.checkExpr(check.tree.viewOf(arm_node).match_arm.body, hint);
        }
        return .poison;
    };

    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);
    const labels = try matchLabels(check, node, view, subject);

    if (subject.held) |held| {
        const chosen = for (view.arms, 0..) |_, position| {
            if (comp.pool.covers(comp.pool.scratch.items[mark + position], held)) break position;
        } else labels.otherwise orelse {
            if (subject.set == null) try check.failToken(check.tree.nodeMainToken(node), .{
                .code = .missing_arm,
                .message = try comp.fmt("this match has no arm for '{s}'", .{
                    try comp.typeName(held),
                }),
                .label = "no arm names it",
                .help = "add an arm naming it, or 'else =>' for the rest",
            });
            return .poison;
        };

        const facts_mark: u32 = @intCast(comp.scratch.facts.items.len);
        defer comp.scratch.facts.shrinkRetainingCapacity(facts_mark);

        const arm_type = comp.pool.scratch.items[mark + chosen];
        if (subject.narrows) |narrows| {
            if (arm_type != .poison) try comp.scratch.facts.append(comp.gpa, .{
                .name = narrows.name,
                .type = arm_type,
                .node = view.arms[chosen],
            });
        }
        const proved: Compilation.Range = .{
            .start = facts_mark,
            .len = @intCast(comp.scratch.facts.items.len - facts_mark),
        };
        const arm = check.tree.viewOf(view.arms[chosen]).match_arm;
        return checkChosen(check, arm.body.toOptional(), proved, hint);
    }

    const builder = check.body();
    try check.reopenDead();
    const entry_reachable = builder.reachable;
    const narrows_mark = comp.scratch.narrows.items.len;

    // the last arm skips its test, exhaustiveness makes it the fall-through
    const last = lastArm(check.tree, view.arms) orelse return .poison;

    var join = try Join.open(check, "match", node, wantsValue(hint), hint, .none);
    const join_block = try check.newBlock();
    var join_reachable = false;
    var all_diverged = true;

    for (view.arms, 0..) |arm_node, position| {
        if (check.tree.nodeTag(arm_node) != .match_arm) continue;
        const arm = check.tree.viewOf(arm_node).match_arm;
        const arm_type = comp.pool.scratch.items[mark + position];

        const arm_block = try check.newBlock();
        var resume_chain: ?IR.Block.Index = null;
        if (position == last) {
            check.endBlock(.{ .jump = arm_block });
        } else {
            const chain = try check.newBlock();
            if (arm_type == .poison) {
                check.endBlock(.{ .jump = chain });
            } else {
                // the compiler's own test, typed void, so no 'bool' is asked of the file
                const holds = try check.emit(arm_node, .union_is, .void_type, .{
                    .probe = .{ .operand = subject.ref, .member = arm_type },
                });
                check.endBlock(.{ .branch = .{
                    .cond = holds,
                    .then_block = arm_block,
                    .else_block = chain,
                } });
            }
            resume_chain = chain;
        }

        check.startBlock(arm_block);
        builder.reachable = entry_reachable;
        if (subject.narrows) |narrows| {
            if (arm_type != .poison) {
                try Narrowing.applyFact(check, .{ .name = narrows.name, .type = arm_type, .node = arm_node });
            }
        }
        const arm_value = try check.checkExpr(arm.body, join.armHint());
        comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);
        if (arm_value != .diverged) {
            all_diverged = false;
            try join.take(check, arm_value, arm.body);
            if (join.carries == false) try check.expectNothing(arm.body, arm_value);
        }

        if (check.jumpTo(join_block)) {
            join_reachable = true;
            if (arm_type != .poison) try comp.pool.scratch.append(comp.gpa, arm_type);
        }
        if (resume_chain) |chain| check.startBlock(chain);
    }

    check.startBlock(join_block);
    builder.reachable = join_reachable;

    if (subject.narrows) |narrows| {
        if (labels.clean and join_reachable) {
            const survivors = comp.pool.scratch.items[mark + view.arms.len ..];
            if (try membersWhere(check, narrows.set, survivors, .covered)) |kept| {
                if (kept != narrows.set) {
                    try Narrowing.applyFact(check, .{ .name = narrows.name, .type = kept, .node = node });
                }
            }
        }
    }
    return join.close(check, all_diverged);
}

const Labels = struct { otherwise: ?usize, clean: bool };

fn matchLabels(
    check: *Check,
    node: Node.Index,
    view: AST.View.Match,
    subject: Subject,
) Allocator.Error!Labels {
    const comp = check.comp;
    const mark = comp.pool.scratch.items.len;
    var otherwise: ?usize = null;
    var clean = true;

    for (view.arms, 0..) |arm_node, position| {
        const arm_type: Pool.Index = blk: {
            if (check.tree.nodeTag(arm_node) != .match_arm) break :blk .poison;
            const label_node = check.tree.viewOf(arm_node).match_arm.label.unwrap() orelse {
                if (otherwise != null) break :blk try failArmAfterElse(check, arm_node);
                otherwise = position;
                const set = subject.set orelse break :blk .poison;
                const earlier = comp.pool.scratch.items[mark..];
                break :blk try membersWhere(check, set, earlier, .uncovered) orelse {
                    try check.fail(arm_node, .{
                        .code = .duplicate_arm,
                        .message = "every member is already handled, so 'else' can never run",
                        .label = "nothing left for it",
                    });
                    break :blk .poison;
                };
            };
            const label = try Resolve.resolveType(check, label_node);
            if (label == .poison) break :blk .poison;
            if (otherwise != null) break :blk try failArmAfterElse(check, label_node);
            if (subject.set) |set| {
                if (try Narrowing.labelWithin(check, label_node, label, set) == false) break :blk .poison;
            }
            if (try matchRepeat(check, view.arms, label_node, label, mark)) break :blk .poison;
            break :blk label;
        };
        if (arm_type == .poison) clean = false;
        try comp.pool.scratch.append(comp.gpa, arm_type);
    }

    if (subject.set) |set| {
        if (clean) {
            const covered = comp.pool.scratch.items[mark..];
            if (try checkMatchMissing(check, node, set, covered)) clean = false;
        }
    }
    return .{ .otherwise = otherwise, .clean = clean };
}

fn coveredByAny(pool: *const Pool, sets: []const Pool.Index, member: Pool.Index) bool {
    for (sets) |set| if (pool.covers(set, member)) return true;
    return false;
}

fn membersWhere(
    check: *Check,
    set: Pool.Index,
    sets: []const Pool.Index,
    which: enum { covered, uncovered },
) Allocator.Error!?Pool.Index {
    const comp = check.comp;
    var kept: [Pool.union_members_max]Pool.Index = undefined;
    var count: u32 = 0;
    for (comp.pool.unionMembers(set)) |member| {
        if (coveredByAny(&comp.pool, sets, member) != (which == .covered)) continue;
        kept[count] = member;
        count += 1;
    }
    if (count == 0) return null;
    if (count == 1) return kept[0];
    return try comp.pool.intern(comp.gpa, .{ .type_union = kept[0..count] });
}

fn matchRepeat(
    check: *Check,
    arms: []const Node.Index,
    label_node: Node.Index,
    label: Pool.Index,
    mark: usize,
) Allocator.Error!bool {
    const comp = check.comp;
    const earlier = comp.pool.scratch.items[mark..];
    const named: []const Pool.Index = if (comp.pool.isUnion(label))
        comp.pool.unionMembers(label)
    else
        &.{label};

    for (named) |member| {
        for (earlier, 0..) |arm_type, position| {
            if (comp.pool.covers(arm_type, member) == false) continue;
            const first = arms[position];
            const first_label = check.tree.viewOf(first).match_arm.label;
            try check.fail(label_node, .{
                .code = .duplicate_arm,
                .message = try comp.fmt("'{s}' is already handled by an earlier arm", .{
                    try comp.typeName(member),
                }),
                .label = "handled again here",
                .notes = try check.noteHere(first_label.unwrap() orelse first, "handled here"),
            });
            return true;
        }
    }
    return false;
}

fn lastArm(tree: *const AST, arms: []const Node.Index) ?usize {
    var index = arms.len;
    while (index > 0) {
        index -= 1;
        if (tree.nodeTag(arms[index]) == .match_arm) return index;
    }
    return null;
}

fn failArmAfterElse(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .duplicate_arm,
        .message = "'else' already takes every type the arms do not name",
        .label = "never runs",
    });
    return .poison;
}

fn checkMatchMissing(
    check: *Check,
    node: Node.Index,
    set: Pool.Index,
    covered: []const Pool.Index,
) Allocator.Error!bool {
    const comp = check.comp;

    const named_max = 5;
    var missing_count: u32 = 0;
    var names: []const u8 = "";
    for (comp.pool.unionMembers(set)) |member| {
        if (coveredByAny(&comp.pool, covered, member)) continue;
        missing_count += 1;
        if (missing_count > named_max) continue;
        names = try quotedList(comp, names, try comp.typeName(member));
    }
    if (missing_count == 0) return false;

    const message = if (missing_count > named_max)
        try comp.fmt("this match leaves out {s}, and {d} more members", .{
            names,
            missing_count - named_max,
        })
    else
        try comp.fmt("this match leaves out {s}", .{names});
    try check.failToken(check.tree.nodeMainToken(node), .{
        .code = .missing_arm,
        .message = message,
        .label = "not every member is handled",
        .help = "add an arm per member, or 'else =>' for the rest",
    });
    return true;
}

fn conditionTruth(check: *const Check, cond: Ref) ?bool {
    return switch (cond.unwrap()) {
        .inst => null,
        .constant => |value| if (value == .poison) null else check.comp.pool.holdsFirst(value),
    };
}

fn checkCondition(check: *Check, node: Node.Index) Allocator.Error!Ref {
    const value = try check.checkValue(node, null);
    const found = check.typeOf(value);
    if (found == .poison) return broken_ref;
    if (check.comp.pool.isUnion(found)) return refOf(value);
    try check.fail(node, .{
        .code = .not_a_union,
        .message = try check.comp.fmt("this condition is {s}, and a condition is a union", .{
            try check.comp.typeName(found),
        }),
        .label = "cannot answer",
        .help = "a condition asks whether a union holds its first member",
    });
    return broken_ref;
}

pub fn checkReturn(
    check: *Check,
    node: Node.Index,
    operand: Node.OptionalIndex,
) Allocator.Error!Value {
    const builder = check.body();
    if (builder.in_defer) {
        try failDeferLeaves(check, node, "no 'return' here");
        return .poison;
    }

    if (operand.unwrap()) |value_node| {
        if (builder.return_type == .void_type) {
            try check.fail(node, .{
                .code = .type_mismatch,
                .message = "this function returns nothing, and this 'return' carries a value",
                .label = "nothing expected",
                .help = "drop the value, or give the function a return type",
            });
            _ = try check.checkExpr(value_node, null);
            check.endBlock(.{ .ret = .none });
            return .diverged;
        }
        const value = try check.checkExpr(value_node, builder.return_type);
        const met = try check.coerce(value, builder.return_type, value_node);
        if (check.blockOpen() == false) return .diverged;
        try check.unwindScopesTo(0);
        check.endBlock(.{ .ret = refOf(met) });
        return .diverged;
    }

    if (builder.return_type != .void_type) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = try check.comp.fmt("'return' here must carry a {s}", .{
                try check.comp.typeName(builder.return_type),
            }),
            .label = "returns nothing",
        });
    }
    try check.unwindScopesTo(0);
    check.endBlock(.{ .ret = .none });
    return .diverged;
}

pub fn checkBreak(check: *Check, node: Node.Index, view: AST.View.Break) Allocator.Error!Value {
    const builder = check.body();

    const frame_index = try findLoop(check, node, view.label) orelse {
        if (view.value.unwrap()) |value_node| _ = try check.checkExpr(value_node, null);
        return .poison;
    };
    const frame = loopPtr(check, frame_index).*;

    if (view.value.unwrap()) |value_node| {
        if (frame.join.carries) {
            const value = try check.checkExpr(value_node, frame.join.armHint());
            if (check.blockOpen() == false) return .diverged;
            try loopPtr(check, frame_index).join.take(check, value, value_node);
        } else {
            try check.fail(node, .{
                .code = .type_mismatch,
                .message = "this 'break' carries a value, and its loop is not asked for one",
                .label = "nothing takes it",
                .help = "bind the loop, as in 'let v = loop { ... }', or drop the value",
            });
            _ = try check.checkExpr(value_node, null);
            if (check.blockOpen() == false) return .diverged;
        }
    } else if (frame.join.carries) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this loop stands where a value is needed, so 'break' must carry it",
            .label = "carries nothing",
        });
    }

    try check.unwindScopesTo(frame.scope_depth);
    if (builder.reachable) loopPtr(check, frame_index).broke_reachable = true;
    check.endBlock(.{ .jump = frame.exit });
    return .diverged;
}

pub fn checkContinue(check: *Check, node: Node.Index, label: ?Token.Index) Allocator.Error!Value {
    const frame_index = try findLoop(check, node, label) orelse return .poison;
    const frame = loopPtr(check, frame_index).*;
    try check.unwindScopesTo(frame.scope_depth);
    check.endBlock(.{ .jump = frame.header });
    return .diverged;
}

fn loopPtr(check: *Check, index: usize) *Check.Builder.LoopFrame {
    const builder = check.body();
    assert(index < builder.loops.items.len);
    return &builder.loops.items[index];
}

fn findLoop(check: *Check, node: Node.Index, label: ?Token.Index) Allocator.Error!?usize {
    const builder = check.body();
    const found: ?usize = found: {
        const token = label orelse {
            if (builder.loops.items.len == 0) break :found null;
            break :found builder.loops.items.len - 1;
        };
        const name = try check.comp.pool.string(check.comp.gpa, check.tree.tokenSlice(token));
        var index = builder.loops.items.len;
        while (index > 0) {
            index -= 1;
            if (builder.loops.items[index].label == name) break :found index;
        }
        break :found null;
    };

    const escapes_defer = if (found) |at| at < builder.defer_loops_floor else true;
    if (builder.in_defer and escapes_defer) {
        try failDeferLeaves(check, node, "not allowed here");
        return null;
    }
    if (found != null) return found;

    if (label) |token| {
        try check.fail(node, .{
            .code = .outside_loop,
            .message = try check.comp.fmt("no enclosing loop is labeled ':{s}'", .{
                check.tree.tokenSlice(token),
            }),
            .label = "no such loop",
        });
    } else {
        try check.fail(node, .{
            .code = .outside_loop,
            .message = "there is no loop here to leave",
            .label = "outside every loop",
        });
    }
    return null;
}

fn failDeferLeaves(check: *Check, node: Node.Index, label: []const u8) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .defer_cannot_leave,
        .message = "a 'defer' runs on the way out, so it cannot leave again",
        .label = label,
    });
}

pub fn checkShortCircuit(
    check: *Check,
    node: Node.Index,
    view: AST.View.Binary,
) Allocator.Error!Value {
    assert(view.op == .bool_and);
    const comp = check.comp;
    const lhs = try check.checkExpr(view.lhs, null);
    const bools = try check.boolType(view.lhs);
    const lhs_met = try check.coerce(lhs, bools, view.lhs);
    if (lhs_met == .poison) {
        try checkAside(check, view.rhs);
        return .poison;
    }

    if (lhs_met == .constant) {
        const truth = check.truthOf(bools, lhs_met.constant) orelse return .poison;
        // the constant decided, so the dead side never runs and never gets checked
        if (truth == false) return lhs_met;
        const rhs = try check.checkExpr(view.rhs, null);
        return check.coerce(rhs, bools, view.rhs);
    }

    const slot = try check.emitSlot(node, .empty, bools);
    try check.emitStore(node, slot, refOf(lhs_met));

    const entry_reachable = check.body().reachable;
    const rhs_block = try check.newBlock();
    const join = try check.newBlock();
    check.endBlock(.{ .branch = .{
        .cond = refOf(lhs_met),
        .then_block = rhs_block,
        .else_block = join,
    } });

    check.startBlock(rhs_block);
    const facts_mark: u32 = @intCast(comp.scratch.facts.items.len);
    defer comp.scratch.facts.shrinkRetainingCapacity(facts_mark);

    const narrows_mark = comp.scratch.narrows.items.len;
    try Narrowing.applyFacts(check, (try Narrowing.gatherFacts(check, view.lhs)).when_true);
    const rhs = try check.checkExpr(view.rhs, null);
    const rhs_met = try check.coerce(rhs, bools, view.rhs);
    if (rhs_met != .diverged) try check.emitStore(view.rhs, slot, refOf(rhs_met));
    comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);
    if (check.blockOpen()) check.endBlock(.{ .jump = join });

    check.startBlock(join);
    check.body().reachable = entry_reachable;
    return check.emitOneValue(node, .load, bools, slot);
}

pub fn checkOr(check: *Check, view: AST.View.Binary, hint: ?Pool.Index) Allocator.Error!Value {
    assert(view.op == .bool_or);
    const lhs = try check.checkValue(view.lhs, hint);
    if (lhs == .diverged) return .diverged;
    if (lhs == .poison) {
        try checkAside(check, view.rhs);
        return .poison;
    }
    const found = check.typeOf(lhs);
    if (check.comp.pool.isUnion(found) == false) {
        try Expr.failNotUnion(check, view.lhs, found, "'or' splits a union");
        try checkAside(check, view.rhs);
        return .poison;
    }
    if (check.builder == null) {
        assert(lhs == .constant);
        return checkOrFold(check, view.rhs, lhs.constant, found);
    }
    return checkOrSplit(check, view.lhs, refOf(lhs), found, view.rhs, .none);
}

fn checkAside(check: *Check, node: Node.Index) Allocator.Error!void {
    const builder = check.builder orelse {
        _ = try check.checkExpr(node, null);
        return;
    };
    const reachable = builder.reachable;
    _ = try check.checkExpr(node, null);
    try check.reopenDead();
    builder.reachable = reachable;
}

fn checkOrFold(
    check: *Check,
    rhs_node: Node.Index,
    lhs: Pool.Index,
    lhs_type: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(check.builder == null);
    assert(comp.pool.typeOfValue(lhs) == lhs_type);

    const first = comp.pool.firstMember(lhs_type);
    if (comp.pool.holdsFirst(lhs)) return .{ .constant = comp.pool.heldValue(lhs) };

    const rhs = try check.checkExpr(rhs_node, first);
    if (check.typeOf(rhs) == lhs_type) return rhs;
    return check.coerce(rhs, first, rhs_node);
}

pub fn checkOrBind(
    check: *Check,
    node: Node.Index,
    view: AST.View.OrBind,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const lhs = try check.checkValue(view.lhs, hint);
    if (lhs.stops()) return lhs;

    const found = check.typeOf(lhs);
    if (comp.pool.isUnion(found) == false) {
        try Expr.failNotUnion(check, node, found, "'or' with a handler splits a union");
        return .poison;
    }
    return checkOrSplit(check, view.lhs, refOf(lhs), found, view.block, view.binder.toOptional());
}

fn checkOrSplit(
    check: *Check,
    lhs_node: Node.Index,
    lhs: Ref,
    lhs_type: Pool.Index,
    rhs_node: Node.Index,
    binder: Node.OptionalIndex,
) Allocator.Error!Value {
    const comp = check.comp;
    const builder = check.body();
    const first = comp.pool.firstMember(lhs_type);
    const rest = try comp.pool.unionTail(comp.gpa, lhs_type);

    const slot = try check.emitSlot(lhs_node, .empty, lhs_type);
    try check.emitStore(lhs_node, slot, lhs);

    const entry_reachable = builder.reachable;
    const rhs_block = try check.newBlock();
    const join = try check.newBlock();
    check.endBlock(.{ .branch = .{
        .cond = lhs,
        .then_block = join,
        .else_block = rhs_block,
    } });

    check.startBlock(rhs_block);
    var widened = false;
    if (binder == .none and orPropagates(check, rhs_node)) {
        const rest_value = try check.emitOne(rhs_node, .union_narrow, rest, lhs);
        const met = try check.coerce(runtimeValue(rest_value, rest), builder.return_type, rhs_node);
        try check.unwindScopesTo(0);
        check.endBlock(.{ .ret = refOf(met) });
    } else {
        const facts_mark: u32 = @intCast(comp.scratch.facts.items.len);
        defer comp.scratch.facts.shrinkRetainingCapacity(facts_mark);

        const narrows_mark = comp.scratch.narrows.items.len;
        const facts = try Narrowing.gatherFacts(check, lhs_node);
        try Narrowing.applyFacts(check, facts.when_false);

        if (binder.unwrap()) |binder_node| {
            try check.pushScope();
            try bindRest(check, binder_node, lhs, rest);
        }
        const rhs = try check.checkExpr(rhs_node, first);
        if (binder != .none) check.popScope();

        widened = check.typeOf(rhs) == lhs_type;
        const met = if (widened) rhs else try check.coerce(rhs, first, rhs_node);
        if (met != .diverged) {
            const settled = if (widened or met == .poison)
                refOf(met)
            else
                try check.emit(rhs_node, .union_init, lhs_type, .{
                    .probe = .{ .operand = refOf(met), .member = first },
                });
            try check.emitStore(rhs_node, slot, settled);
        }
        comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);
        if (check.blockOpen()) check.endBlock(.{ .jump = join });
    }

    check.startBlock(join);
    builder.reachable = entry_reachable;
    const loaded = try check.emitOne(lhs_node, .load, lhs_type, slot);
    if (widened) return runtimeValue(loaded, lhs_type);
    return check.emitOneValue(lhs_node, .union_narrow, first, loaded);
}

fn orPropagates(check: *const Check, node: Node.Index) bool {
    if (check.tree.nodeTag(node) != .return_expr) return false;
    if (check.body().return_type == .void_type) return false;
    if (check.body().in_defer) return false;
    return check.tree.viewOf(node).return_expr == .none;
}

fn bindRest(
    check: *Check,
    binder_node: Node.Index,
    lhs: Ref,
    rest: Pool.Index,
) Allocator.Error!void {
    const text = check.mainTokenText(binder_node);
    if (Module.isDiscard(text)) return check.failDiscard(binder_node);
    const name = try check.comp.pool.string(check.comp.gpa, text);
    const narrowed = try check.emitOne(binder_node, .union_narrow, rest, lhs);
    try check.declareLocal(name, binder_node, .let, narrowed, rest);
}
