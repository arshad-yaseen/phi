//! Runs a body at check time.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Check = @import("Check.zig");
const Compilation = @import("Compilation.zig");
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
refusal: Refusal = .none,

const Comptime = @This();

const Error = Allocator.Error || error{Refused};

/// What a body did instead of answering, said in the words of the report.
const Refusal = union(enum) {
    none,
    /// The program stopped itself, which at run time would be a trap.
    trapped,
    /// A limit a written program can reach, so it is named where it is spent.
    spent,
    /// An instruction that has no meaning before the program runs.
    runtime: []const u8,
};

/// The call's answer, or poison where it was refused and reported.
pub fn call(
    check: *Check,
    node: Node.Index,
    instance: Pool.Instance,
    args: []const Pool.Index,
) Allocator.Error!Value {
    var evaluator: Comptime = .{
        .check = check,
        .node = node,
        .bools = try check.boolType(node),
    };
    if (evaluator.bools == .poison) return .poison;

    const answer = evaluator.run(instance, args) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Refused => return evaluator.report(),
    };
    return .{ .constant = answer };
}

fn report(evaluator: *Comptime) Allocator.Error!Value {
    const check = evaluator.check;
    return switch (evaluator.refusal) {
        .none => unreachable, // a refusal always says what it was
        .trapped => check.refuse(evaluator.node, .{
            .code = .comptime_trapped,
            .message = "this call stops the program, and the compiler ran it",
            .label = "stopped here",
            .help = "a call that must settle before anything runs cannot trap",
        }),
        .spent => check.refuse(evaluator.node, .{
            .code = .comptime_too_long,
            .message = try check.comp.fmt(
                "this call takes more than {d} loops and calls to settle",
                .{budget},
            ),
            .label = "did not settle",
        }),
        .runtime => |what| check.refuse(evaluator.node, .{
            .code = .not_constant,
            .message = try check.comp.fmt(
                "this must settle before anything runs, and {s} happens at run time",
                .{what},
            ),
            .label = "not a constant",
        }),
    };
}

fn refuse(evaluator: *Comptime, refusal: Refusal) Error {
    @branchHint(.cold);
    if (evaluator.refusal == .none) evaluator.refusal = refusal;
    return error.Refused;
}

fn spend(evaluator: *Comptime) Error!void {
    evaluator.spent += 1;
    if (evaluator.spent > budget) return evaluator.refuse(.spent);
}

/// What each instruction answered. A `local` answers nothing and uses `slots`.
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
    if (comp.ranCall(instance, args)) |answer| return answer;

    const answer = try evaluator.evaluate(instance, args);
    try comp.keepCall(instance, args, answer);
    return answer;
}

fn evaluate(evaluator: *Comptime, instance: Pool.Instance, args: []const Pool.Index) Error!Pool.Index {
    const comp = evaluator.check.comp;
    if (evaluator.depth == depth_max) return evaluator.refuse(.spent);

    const decl = comp.declAt(comp.instanceDecl(instance));
    if (decl.kind == .extern_fn) return evaluator.refuse(.{ .runtime = "a call the linker resolves" });

    try comp.ensure(.of(.body, instance), .{ .module = decl.module, .node = decl.node });
    const func_index = comp.instanceAt(instance).func.unwrap() orelse
        return evaluator.refuse(.{ .runtime = "a call" });
    const func = comp.funcAt(func_index);

    const gpa = comp.gpa;
    const values = try gpa.alloc(Pool.Index, func.insts.len);
    defer gpa.free(values);
    const slots = try gpa.alloc(Pool.Index, func.insts.len);
    defer gpa.free(slots);
    @memset(values, .poison);
    @memset(slots, .poison);

    // the body opens with one `param` per row, which the call already settled
    assert(args.len <= func.insts.len);
    for (args, 0..) |argument, position| values[position] = argument;

    const frame: Frame = .{ .func = func, .values = values, .slots = slots };

    evaluator.depth += 1;
    defer evaluator.depth -= 1;

    var block: u32 = 0;
    while (true) {
        // read afresh, because a call inside the body grows what this points into
        const here = comp.funcBlocks(func)[block];
        var at = here.first;
        while (at < here.end()) : (at += 1) try evaluator.step(frame, at);

        switch (here.terminator) {
            .jump => |to| {
                if (to.int() <= block) try evaluator.spend();
                block = to.int();
            },
            .branch => |it| {
                const holds = evaluator.truth(frame.at(it.cond));
                const to = if (holds) it.then_block else it.else_block;
                if (to.int() <= block) try evaluator.spend();
                block = to.int();
            },
            .ret => |ref| return if (ref == .none) .poison else frame.at(ref),
            .trap => return evaluator.refuse(.trapped),
        }
    }
}

/// Whether a condition holds its union's first member, which is the then edge.
fn truth(evaluator: *const Comptime, cond: Pool.Index) bool {
    const pool = &evaluator.check.comp.pool;
    return pool.memberOfValue(cond) == pool.firstMember(pool.typeOfValue(cond));
}

fn step(evaluator: *Comptime, frame: Frame, at: u32) Error!void {
    const comp = evaluator.check.comp;
    const inst = comp.instAt(frame.func.insts.start + at);
    const answer: Pool.Index = switch (inst.tag) {
        // a param is bound by the call, and a local is its own slot
        .param, .local => return,
        .store => {
            const it = inst.data.bin;
            const slot = switch (it.lhs.unwrap()) {
                .inst => |slot| slot,
                .constant => return evaluator.refuse(.{ .runtime = "a write through a pointer" }),
            };
            frame.slots[slot.int()] = frame.at(it.rhs);
            return;
        },
        .load => switch (inst.data.un.unwrap()) {
            .inst => |slot| frame.slots[slot.int()],
            .constant => return evaluator.refuse(.{ .runtime = "a read through a pointer" }),
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
        => try evaluator.binary(frame, inst),

        .negate => try evaluator.settle(try comp.pool.foldNegate(
            comp.gpa,
            frame.at(inst.data.un),
        )),
        .bit_not => try evaluator.settle(try comp.pool.foldBitNot(
            comp.gpa,
            frame.at(inst.data.un),
        )),
        .not => try evaluator.truthValue(evaluator.truth(frame.at(inst.data.un)) == false),

        .widen => switch (try comp.pool.fit(comp.gpa, frame.at(inst.data.un), inst.type, .allowed)) {
            .value => |value| value,
            // the checker admitted this widening, so nothing here can lose a value
            .does_not_fit, .wrong_kind => unreachable,
        },
        .int_cast => try evaluator.intCast(frame.at(inst.data.un), inst.type),
        .int_fits => try evaluator.intFits(frame.at(inst.data.un), inst.type),

        .union_init => try evaluator.wrap(inst.type, frame.at(inst.data.probe.operand)),
        .union_is => was: {
            const held = comp.pool.memberOfValue(frame.at(inst.data.probe.operand));
            const holds = comp.pool.covers(inst.data.probe.member, held);
            break :was try evaluator.truthValue(holds);
        },
        .union_narrow => try evaluator.narrow(frame.at(inst.data.un), inst.type),

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
        => return evaluator.refuse(.{ .runtime = "reaching through an address" }),
    };
    frame.values[at] = answer;
}

fn binary(evaluator: *Comptime, frame: Frame, inst: IR.Inst) Error!Pool.Index {
    const comp = evaluator.check.comp;
    const op: AST.BinaryOp = switch (inst.tag) {
        .add => .add,
        .sub => .sub,
        .mul => .mul,
        .div => .div,
        .mod => .mod,
        .bit_and => .bit_and,
        .bit_or => .bit_or,
        .bit_xor => .bit_xor,
        .shift_left => .shift_left,
        .shift_right => .shift_right,
        .cmp_eq => .equal,
        .cmp_ne => .not_equal,
        .cmp_lt => .less_than,
        .cmp_le => .less_or_equal,
        .cmp_gt => .greater_than,
        .cmp_ge => .greater_or_equal,
        else => unreachable, // every other tag is answered by its own arm
    };
    const it = inst.data.bin;
    return evaluator.settle(try comp.pool.fold(comp.gpa, op, frame.at(it.lhs), frame.at(it.rhs)));
}

/// A fold the checker would take as a value. Anything else must stop the run.
fn settle(evaluator: *Comptime, folded: Pool.Fold) Error!Pool.Index {
    return switch (folded) {
        .value => |value| value,
        .truth => |holds| try evaluator.truthValue(holds),
        .overflow, .division_by_zero, .bad_shift, .does_not_fit => evaluator.refuse(.trapped),
        // the checker settled the types before ever lowering the operation
        .mismatch, .bad_operand => unreachable,
    };
}

fn truthValue(evaluator: *Comptime, holds: bool) Allocator.Error!Pool.Index {
    const pool = &evaluator.check.comp.pool;
    const member = pool.unionMemberAt(evaluator.bools, if (holds) 0 else 1);
    return evaluator.wrap(evaluator.bools, try pool.intern(
        evaluator.check.comp.gpa,
        .{ .value_unit = member },
    ));
}

fn wrap(evaluator: *Comptime, union_type: Pool.Index, held: Pool.Index) Allocator.Error!Pool.Index {
    const comp = evaluator.check.comp;
    return comp.pool.intern(comp.gpa, .{ .value_union = .{ .type = union_type, .value = held } });
}

fn narrow(evaluator: *Comptime, value: Pool.Index, wanted: Pool.Index) Allocator.Error!Pool.Index {
    const pool = &evaluator.check.comp.pool;
    const held = pool.heldValue(value);
    if (pool.isUnion(wanted) == false) return held;
    return evaluator.wrap(wanted, held);
}

fn intCast(evaluator: *Comptime, value: Pool.Index, wanted: Pool.Index) Error!Pool.Index {
    const comp = evaluator.check.comp;
    const written = comp.pool.keyOf(value).value_int.value;
    if (Pool.fitsInt(written, wanted) == false) return evaluator.refuse(.trapped);
    return comp.pool.intern(comp.gpa, .{ .value_int = .{ .type = wanted, .value = written } });
}

fn intFits(evaluator: *Comptime, value: Pool.Index, result: Pool.Index) Allocator.Error!Pool.Index {
    const comp = evaluator.check.comp;
    const wanted = comp.pool.unionMemberAt(result, 0);
    const written = comp.pool.keyOf(value).value_int.value;
    const held = if (Pool.fitsInt(written, wanted))
        try comp.pool.intern(comp.gpa, .{ .value_int = .{ .type = wanted, .value = written } })
    else
        try comp.pool.intern(comp.gpa, .{
            .value_unit = comp.pool.unionMemberAt(result, 1),
        });
    return evaluator.wrap(result, held);
}

fn callAt(evaluator: *Comptime, frame: Frame, inst: IR.Inst) Error!Pool.Index {
    const comp = evaluator.check.comp;
    try evaluator.spend();

    const it = IR.callAt(comp.funcExtra(frame.func), inst.data.payload);
    const args = try comp.gpa.alloc(Pool.Index, it.args.len);
    defer comp.gpa.free(args);
    for (it.args, args) |argument, *slot| slot.* = frame.at(argument);

    return evaluator.run(it.callee, args);
}
