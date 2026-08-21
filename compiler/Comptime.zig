//! Runs a body at check time.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Check = @import("Check.zig");
const Diagnostic = @import("Diagnostic.zig");
const IR = @import("IR.zig");
const Pool = @import("Pool.zig");

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

/// A call's arguments. The receiver is one more than a call may write.
const Args = [Check.call_args_max + 1]Pool.Index;

/// The call's answer, or poison where it was refused and reported.
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

/// The program stopped itself, which at run time would be a trap.
fn trapped(evaluator: *Comptime) Error {
    return evaluator.refuse(.{
        .code = .comptime_trapped,
        .message = "this call stops the program, and the compiler ran it",
        .label = "stopped here",
        .help = "a call that must settle before anything runs cannot trap",
    });
}

/// A limit a written program can reach, so it is named where it is spent.
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

/// An instruction that has no meaning before the program runs.
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

/// What each instruction answered, and what each `local` holds.
const Frame = struct {
    func: IR.Func,
    values: []Pool.Index,
    slots: []Pool.Index,

    fn at(frame: Frame, ref: IR.Ref) Pool.Index {
        return switch (ref.unwrap()) {
            .constant => |constant| constant,
            .inst => |inst| frame.values[inst.int()],
        };
    }
};

/// The answer a call gives, run once however often the program writes it.
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

    try comp.ensure(.of(.body, instance), .{ .module = decl.module, .node = decl.node });
    const func_index = comp.instanceAt(instance).func.unwrap() orelse
        return evaluator.runtime("a call");
    const func = comp.funcAt(func_index);

    const cells = try comp.gpa.alloc(Pool.Index, 2 * func.insts.len);
    defer comp.gpa.free(cells);
    @memset(cells, .poison);
    const frame: Frame = .{
        .func = func,
        .values = cells[0..func.insts.len],
        .slots = cells[func.insts.len..],
    };

    // the body opens with one `param` per row, which the call already settled
    assert(args.len <= func.insts.len);
    @memcpy(frame.values[0..args.len], args);

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
            .branch => |it| if (comp.pool.holdsFirst(frame.at(it.cond)))
                it.then_block
            else
                it.else_block,
            .ret => |ref| return if (ref == .none) .poison else frame.at(ref),
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
        // a param is bound by the call, and a local is its own slot
        .param, .local => return,
        .store => {
            const it = inst.data.bin;
            const slot = switch (it.lhs.unwrap()) {
                .inst => |slot| slot,
                .constant => return evaluator.runtime("a write through a pointer"),
            };
            frame.slots[slot.int()] = frame.at(it.rhs);
            return;
        },
        .load => switch (inst.data.un.unwrap()) {
            .inst => |slot| frame.slots[slot.int()],
            .constant => return evaluator.runtime("a read through a pointer"),
        },

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
            const folded = try pool.fold(gpa, tag.binaryOp(), frame.at(it.lhs), frame.at(it.rhs));
            break :folded try evaluator.settle(folded);
        },
        .negate => try evaluator.settle(try pool.foldNegate(gpa, frame.at(inst.data.un))),
        .bit_not => try evaluator.settle(try pool.foldBitNot(gpa, frame.at(inst.data.un))),
        .not => try pool.truth(gpa, evaluator.bools, !pool.holdsFirst(frame.at(inst.data.un))),

        // the checker admitted this widening, so nothing here can lose a value
        .widen => (try pool.fit(gpa, frame.at(inst.data.un), inst.type, .allowed)).value,
        .int_cast => try pool.castInt(gpa, frame.at(inst.data.un), inst.type) orelse
            return evaluator.trapped(),
        .int_fits => fitted: {
            const wanted = pool.unionMemberAt(inst.type, 0);
            const held = try pool.castInt(gpa, frame.at(inst.data.un), wanted) orelse
                try pool.unitValue(gpa, pool.unionMemberAt(inst.type, 1));
            break :fitted try pool.enter(gpa, inst.type, held);
        },

        .union_init => try pool.enter(gpa, inst.type, frame.at(inst.data.probe.operand)),
        .union_is => was: {
            const held = pool.memberOfValue(frame.at(inst.data.probe.operand));
            const holds = pool.covers(inst.data.probe.member, held);
            break :was try pool.truth(gpa, evaluator.bools, holds);
        },
        .union_narrow => try pool.narrowTo(gpa, frame.at(inst.data.un), inst.type),

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
    frame.values[at] = answer;
}

/// A fold the checker would take as a value. Anything else must stop the run.
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
    for (it.args, args[0..it.args.len]) |argument, *slot| slot.* = frame.at(argument);
    return evaluator.run(it.callee, args[0..it.args.len]);
}
