//! Runs a body at check time.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Check = @import("../Check.zig");
const Diagnostic = @import("../Diagnostic.zig");
const IR = @import("../IR.zig");
const Pool = @import("../Pool.zig");

const Node = AST.Node;
const Value = Check.Value;

/// Back edges and calls one evaluation may spend.
const budget = 1000;

/// Frames one evaluation may stack, which a body that recurses without end reaches.
const depth_max = 64;

check: *Check,
node: Node.Index,
bools: Pool.Index,
spent: u32 = 0,
depth: u32 = 0,

const Comptime = @This();

const Error = Allocator.Error || error{Refused};

/// The receiver is one more than a call may write.
const Args = [Check.call_args_max + 1]Pool.Index;

pub fn call(
    check: *Check,
    node: Node.Index,
    instance: Pool.Instance,
    operands: []const Check.Operand,
) Allocator.Error!Value {
    var args: Args = undefined;
    assert(operands.len <= args.len);
    for (operands, args[0..operands.len]) |operand, *argument| {
        if (operand.value != .constant) return check.needRuntime(node, "this argument");
        argument.* = operand.value.constant;
    }

    var evaluator: Comptime = .{ .check = check, .node = node, .bools = try check.boolType(node) };
    if (evaluator.bools == .poison) return .poison;
    const answer = evaluator.run(instance, args[0..operands.len]) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Refused => return .poison,
    };
    return .{ .constant = answer };
}

fn refuse(evaluator: *Comptime, report: Diagnostic.Report) Error {
    @branchHint(.cold);
    try evaluator.check.fail(evaluator.node, report);
    return error.Refused;
}

fn trapped(evaluator: *Comptime) Error {
    return evaluator.refuse(.{
        .code = .comptime_trapped,
        .message = "this call stops the program, and the compiler ran it",
        .label = "stopped here",
        .help = "a call that must settle before anything runs cannot trap",
    });
}

fn tooLong(evaluator: *Comptime) Error {
    return evaluator.refuse(.{
        .code = .comptime_too_long,
        .message = try evaluator.check.comp.fmt(
            "this call takes more than {d} loops and calls to settle",
            .{budget},
        ),
        .label = "did not settle",
    });
}

fn runtime(evaluator: *Comptime, what: []const u8) Error {
    return evaluator.refuse(.{
        .code = .not_constant,
        .message = try evaluator.check.comp.fmt(
            "this must settle before anything runs, and {s} happens at run time",
            .{what},
        ),
        .label = "not a constant",
    });
}

fn spend(evaluator: *Comptime) Error!void {
    evaluator.spent += 1;
    if (evaluator.spent > budget) return evaluator.tooLong();
}

const Frame = struct {
    evaluator: *Comptime,
    func: IR.Func,
    cells: []Pool.Index,

    fn at(frame: Frame, ref: IR.Ref) Error!Pool.Index {
        const inst = switch (ref.unwrap()) {
            .constant => |constant| return constant,
            .inst => |inst| inst,
        };
        // a local's ref is its address, which no constant spells
        if (frame.tagOf(inst) == .local) return frame.evaluator.runtime("taking an address");
        return frame.cells[inst.int()];
    }

    /// The cell a pointer reaches, which is a local's own and nothing else's.
    fn slot(frame: Frame, ref: IR.Ref, what: []const u8) Error!*Pool.Index {
        switch (ref.unwrap()) {
            .inst => |inst| if (frame.tagOf(inst) == .local) return &frame.cells[inst.int()],
            .constant => {},
        }
        return frame.evaluator.runtime(what);
    }

    fn tagOf(frame: Frame, inst: IR.Inst.Index) IR.Inst.Tag {
        const tags = frame.evaluator.check.comp.ir.insts.items(.tag);
        return tags[frame.func.insts.at(inst.int())];
    }
};

fn run(evaluator: *Comptime, instance: Pool.Instance, args: []const Pool.Index) Error!Pool.Index {
    const comp = evaluator.check.comp;
    if (comp.calls.get(instance, args)) |answer| return answer;

    const answer = try evaluator.evaluate(instance, args);
    (try comp.calls.getOrPut(comp.gpa, instance, args)).value_ptr.* = answer;
    return answer;
}

fn evaluate(
    evaluator: *Comptime,
    instance: Pool.Instance,
    args: []const Pool.Index,
) Error!Pool.Index {
    const comp = evaluator.check.comp;
    if (evaluator.depth == depth_max) return evaluator.tooLong();

    const decl = comp.declAt(comp.instanceDecl(instance));
    if (decl.kind == .extern_fn) return evaluator.runtime("a call the linker resolves");

    try comp.ensure(.{ .body = instance }, decl.origin());
    const func = comp.funcOf(instance) orelse return evaluator.runtime("a call");

    const cells = try comp.gpa.alloc(Pool.Index, func.insts.len);
    defer comp.gpa.free(cells);
    @memset(cells, .poison);
    const frame: Frame = .{ .evaluator = evaluator, .func = func, .cells = cells };

    // the body opens with one `param` per row, which the call already settled
    assert(args.len <= func.insts.len);
    @memcpy(cells[0..args.len], args);

    evaluator.depth += 1;
    defer evaluator.depth -= 1;

    var block: u32 = 0;
    while (true) {
        // read afresh, because a call inside the body grows what this points into
        const here = comp.funcBlocks(func)[block];
        var at = here.first;
        while (at < here.end()) : (at += 1) try evaluator.step(frame, at);

        const to: IR.Block.Index = switch (here.terminator) {
            .jump => |to| to,
            .branch => |it| if (comp.pool.holdsFirst(try frame.at(it.cond)))
                it.then_block
            else
                it.else_block,
            .ret => |ref| return if (ref == .none) .poison else try frame.at(ref),
            .trap => return evaluator.trapped(),
        };
        if (to.int() <= block) try evaluator.spend();
        block = to.int();
    }
}

fn step(evaluator: *Comptime, frame: Frame, at: u32) Error!void {
    const comp = evaluator.check.comp;
    const pool = &comp.pool;
    const gpa = comp.gpa;
    const inst = comp.instAt(frame.func.insts.start + at);
    const answer: Pool.Index = switch (inst.tag) {
        .param, .local => return,
        .store => {
            const it = inst.data.bin;
            (try frame.slot(it.lhs, "a write through a pointer")).* = try frame.at(it.rhs);
            return;
        },
        .load => (try frame.slot(inst.data.un, "a read through a pointer")).*,

        .add,
        .sub,
        .mul,
        .div,
        .mod,
        .bit_and,
        .bit_or,
        .bit_xor,
        .shift_left,
        .shift_right,
        .cmp_eq,
        .cmp_ne,
        .cmp_lt,
        .cmp_le,
        .cmp_gt,
        .cmp_ge,
        => |tag| folded: {
            const it = inst.data.bin;
            const lhs = try frame.at(it.lhs);
            const rhs = try frame.at(it.rhs);
            break :folded try evaluator.settle(try pool.fold(gpa, tag.binaryOp(), lhs, rhs));
        },
        .negate => try evaluator.settle(try pool.foldNegate(gpa, try frame.at(inst.data.un))),
        .bit_not => try evaluator.settle(try pool.foldBitNot(gpa, try frame.at(inst.data.un))),
        .not => not: {
            const holds = pool.holdsFirst(try frame.at(inst.data.un));
            break :not try pool.truth(gpa, evaluator.bools, !holds);
        },

        // the checker admitted this widening, so nothing here can lose a value
        .widen => (try pool.fit(gpa, try frame.at(inst.data.un), inst.type, .allowed)).value,
        .int_cast => try pool.castInt(gpa, try frame.at(inst.data.un), inst.type) orelse
            return evaluator.trapped(),
        .int_fits => fitted: {
            const wanted = pool.unionMemberAt(inst.type, 0);
            const held = try pool.castInt(gpa, try frame.at(inst.data.un), wanted) orelse
                try pool.unitValue(gpa, pool.unionMemberAt(inst.type, 1));
            break :fitted try pool.enter(gpa, inst.type, held);
        },

        .union_init => try pool.enter(gpa, inst.type, try frame.at(inst.data.probe.operand)),
        .union_is => was: {
            const held = pool.memberOfValue(try frame.at(inst.data.probe.operand));
            const holds = pool.covers(inst.data.probe.member, held);
            break :was try pool.truth(gpa, evaluator.bools, holds);
        },
        .union_narrow => try pool.narrowTo(gpa, try frame.at(inst.data.un), inst.type),

        .call => try evaluator.callAt(frame, inst),

        .bounds_check,
        .order_check,
        .field_ptr,
        .field_val,
        .elem_ptr,
        .slice_len,
        .slice_ptr,
        .slice_make,
        .slice_from,
        .ptr_cast,
        .int_from_ptr,
        .aggregate_init,
        => return evaluator.runtime("reaching through an address"),
    };
    frame.cells[at] = answer;
}

fn settle(evaluator: *Comptime, folded: Pool.Fold) Error!Pool.Index {
    const comp = evaluator.check.comp;
    return switch (folded) {
        .value => |value| value,
        .truth => |holds| try comp.pool.truth(comp.gpa, evaluator.bools, holds),
        .overflow, .division_by_zero, .bad_shift, .does_not_fit => evaluator.trapped(),
        // the checker settled the types before ever lowering the operation
        .mismatch, .bad_operand => unreachable,
    };
}

fn callAt(evaluator: *Comptime, frame: Frame, inst: IR.Inst) Error!Pool.Index {
    try evaluator.spend();

    const it = IR.callAt(evaluator.check.comp.funcExtra(frame.func), inst.data.payload);
    var args: Args = undefined;
    assert(it.args.len <= args.len);
    for (it.args, args[0..it.args.len]) |argument, *slot| slot.* = try frame.at(argument);
    return evaluator.run(it.callee, args[0..it.args.len]);
}
