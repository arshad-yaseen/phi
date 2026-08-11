//! The typed IR, a control-flow graph per function.

const std = @import("std");
const assert = std.debug.assert;

const Compilation = @import("Compilation.zig");
const Pool = @import("Pool.zig");

pub const ExtraIndex = enum(u32) { _ };

pub const InstList = std.MultiArrayList(Inst);

pub const Call = struct { callee: Pool.Instance, args: []const Ref };

/// One body, three ranges into the shared tables, every inner index relative to them.
pub const Func = struct {
    instance: Pool.Instance,
    insts: Compilation.Range,
    /// One `Ref` per word.
    extra: Compilation.Range,
    /// Block zero is the entry, and every block is reachable.
    blocks: Compilation.Range,

    pub const Index = enum(u32) {
        _,

        pub fn from(raw: usize) Index {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(@as(u32, @intCast(raw)));
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }

        pub fn toOptional(index: Index) OptionalIndex {
            const optional: OptionalIndex = @enumFromInt(@intFromEnum(index));
            assert(optional != .none);
            return optional;
        }
    };

    pub const OptionalIndex = enum(u32) {
        none = std.math.maxInt(u32),
        _,

        pub fn unwrap(optional: OptionalIndex) ?Index {
            if (optional == .none) return null;
            return @enumFromInt(@intFromEnum(optional));
        }
    };
};

/// Reads a call payload out of one function's extra words.
pub fn callAt(extra: []const u32, at: ExtraIndex) Call {
    const start = @intFromEnum(at);
    assert(start + 2 <= extra.len);
    return .{
        .callee = @enumFromInt(extra[start]),
        .args = refsAt(extra, start + 2, extra[start + 1]),
    };
}

pub const SliceMake = struct { base: Ref, start: Ref, end: Ref };

/// The base and the two ends.
pub fn sliceMakeAt(extra: []const u32, at: ExtraIndex) SliceMake {
    const start = @intFromEnum(at);
    assert(start + 3 <= extra.len);
    return .{
        .base = @enumFromInt(extra[start]),
        .start = @enumFromInt(extra[start + 1]),
        .end = @enumFromInt(extra[start + 2]),
    };
}

/// Elements in order, or fields in declaration order.
pub fn aggregateInitAt(extra: []const u32, at: ExtraIndex) []const Ref {
    const start = @intFromEnum(at);
    assert(start + 1 <= extra.len);
    return refsAt(extra, start + 1, extra[start]);
}

fn refsAt(extra: []const u32, start: u32, len: u32) []const Ref {
    assert(start + len <= extra.len);
    // a `Ref` is one `u32`
    return @ptrCast(extra[start..][0..len]);
}

/// An instruction result or a pool constant, told apart by the top bit.
pub const Ref = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    const inst_bit: u32 = 1 << 31;

    /// The indexes `fromInst` accepts. One below the bit keeps `none` its encoding.
    pub const inst_count_max: u32 = inst_bit - 1;

    pub fn fromConstant(value: Pool.Index) Ref {
        assert(value.int() < inst_bit);
        return @enumFromInt(value.int());
    }

    pub fn fromInst(inst: Inst.Index) Ref {
        assert(inst.int() < inst_count_max);
        return @enumFromInt(inst.int() | inst_bit);
    }

    pub fn unwrap(ref: Ref) union(enum) { constant: Pool.Index, inst: Inst.Index } {
        assert(ref != .none);
        const raw = @intFromEnum(ref);
        if (raw & inst_bit == 0) return .{ .constant = @enumFromInt(raw) };
        return .{ .inst = @enumFromInt(raw & ~inst_bit) };
    }
};

pub const Inst = struct {
    tag: Tag,
    /// `void_type` for an effect.
    type: Pool.Index,
    data: Data,

    pub const Index = enum(u32) {
        _,

        pub fn from(raw: usize) Index {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(@as(u32, @intCast(raw)));
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }
    };

    pub const Data = union {
        none: void,
        un: Ref,
        bin: struct { lhs: Ref, rhs: Ref },
        field: struct { base: Ref, row: Compilation.Row.Index },
        probe: struct { operand: Ref, member: Pool.Index },
        name: Pool.String,
        payload: ExtraIndex,
    };

    pub const Tag = enum(u8) {
        /// Uses `name`. One per parameter, in order.
        param,
        /// Uses `name`, `.empty` for a temporary. Produces the address.
        local,
        /// Uses `un`, a place. Produces the pointee.
        load,
        /// Uses `bin`. The place, then the value.
        store,
        /// Uses `field`. Produces a field pointer, as mutable as its base.
        field_ptr,
        /// Uses `field`. Produces the field's value.
        field_val,
        /// Uses `bin`, what holds the elements and the index.
        elem_ptr,
        /// Uses `bin`. Sign-widened then compared unsigned, so one test settles both edges.
        ///
        ///   written   widened to 64 bits    read as unsigned      verdict
        ///   i32   3   0x00000000_00000003                     3   3 < 4, passes
        ///   u64   3   0x00000000_00000003                     3   3 < 4, passes
        ///   i32  -1   0xffffffff_ffffffff  18446744073709551615   above 4, traps
        bounds_check,
        /// Uses `bin`, trapping unless the first is at most the second, widened as above.
        order_check,
        /// Uses `un`, a view. Produces the count it carries.
        slice_len,
        /// Uses `payload`, read by `sliceMakeAt`.
        slice_make,

        // all `bin`
        /// Traps where the sum does not fit.
        add,
        /// Traps where the difference does not fit.
        sub,
        /// Traps where the product does not fit.
        mul,
        /// Traps where the quotient does not fit, and where the divisor is zero.
        div,
        /// Traps where the divisor is zero.
        mod,
        bit_and,
        bit_or,
        bit_xor,
        /// Traps where the count is not below the width. Bits shifted out are lost.
        shift_left,
        /// Arithmetic, so a negative value keeps its sign. Traps on the same counts.
        shift_right,
        cmp_eq,
        cmp_ne,
        cmp_lt,
        cmp_le,
        cmp_gt,
        cmp_ge,

        // all `un`
        /// Traps where the negation does not fit, which is the type's lowest value.
        negate,
        not,
        bit_not,

        /// Uses `un`. Retypes a pointer and emits nothing.
        ptr_cast,
        /// Uses `un`. Sign- or zero-extends into a type holding every value of the old one.
        int_widen,
        /// Uses `un`. Widens a float into one holding every value of the old one.
        float_widen,
        /// Uses `un`. The value where its type holds it, and the union's other member where not.
        int_cast,

        /// Uses `un`. A value entering a union that lists it, or a union widening.
        union_init,
        /// Uses `probe`. Void where only a branch reads it.
        union_is,
        /// Uses `un`. A union retyped to what a passed test proved.
        union_narrow,

        /// Uses `payload`, an `IR.Call`.
        call,

        /// Uses `payload`, read by `aggregateInitAt`. An array or a struct, told apart by the type.
        aggregate_init,
    };
};

pub const Block = struct {
    /// Instructions `first ..< end()`, contiguous.
    first: u32,
    count: u32,
    terminator: Terminator,

    pub fn end(block: Block) u32 {
        return block.first + block.count;
    }

    pub const Index = enum(u32) {
        entry = 0,
        _,

        pub fn from(raw: usize) Index {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(@as(u32, @intCast(raw)));
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }
    };
};

pub const Terminator = union(enum) {
    /// Still being built.
    none,
    jump: Block.Index,
    /// The then edge is taken when the union condition holds its first member.
    branch: struct { cond: Ref, then_block: Block.Index, else_block: Block.Index },
    /// `.none` returns nothing.
    ret: Ref,
    /// Stops the program where it stands, so nothing follows it.
    trap,
};

comptime {
    assert(@sizeOf(Inst.Tag) == 1);
    assert(@sizeOf(Ref) == 4);
    if (std.debug.runtime_safety == false) assert(@sizeOf(Inst.Data) == 8);
    assert(@sizeOf(Block) <= 24);
    // the largest instruction ref stays one below `none`, never colliding
    assert(@intFromEnum(Ref.none) == Ref.inst_bit + Ref.inst_count_max);
}
