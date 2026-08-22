//! The typed IR, a control-flow graph per function.

const std = @import("std");
const assert = std.debug.assert;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Handle = @import("Handle.zig");
const Pool = @import("Pool.zig");

pub const ExtraIndex = Handle.Index("inst extra");

pub const InstList = std.MultiArrayList(Inst);

/// What a compilation produces: every lowered body, and the tables they range over.
pub const Program = struct {
    /// The bodies the program runs, in the order it reached them from its entry.
    bodies: []const Pool.Instance = &.{},
    funcs: std.ArrayList(Func) = .empty,
    insts: InstList = .empty,
    extra: std.ArrayList(u32) = .empty,
    blocks: std.ArrayList(Block) = .empty,

    pub fn deinit(program: *Program, gpa: std.mem.Allocator) void {
        inline for (@typeInfo(Program).@"struct".fields) |field| {
            if (@typeInfo(field.type) == .@"struct") @field(program, field.name).deinit(gpa);
        }
        program.* = undefined;
    }
};

pub const Call = struct { callee: Pool.Instance, args: []const Ref };

/// One body, three ranges into the shared tables, every inner index relative.
pub const Func = struct {
    instance: Pool.Instance,
    insts: Compilation.Range,
    extra: Compilation.Range,
    /// Block zero is the entry, and every block is reachable.
    blocks: Compilation.Range,

    pub const Index = Handle.Index("func");
    pub const OptionalIndex = Index.Optional;
};

pub fn callAt(extra: []const u32, at: ExtraIndex) Call {
    const start = @intFromEnum(at);
    assert(start + 2 <= extra.len);
    return .{
        .callee = @enumFromInt(extra[start]),
        .args = refsAt(extra, start + 2, extra[start + 1]),
    };
}

pub const SliceMake = struct { base: Ref, start: Ref, end: Ref };

pub fn sliceMakeAt(extra: []const u32, at: ExtraIndex) SliceMake {
    const start = @intFromEnum(at);
    assert(start + 3 <= extra.len);
    return .{
        .base = @enumFromInt(extra[start]),
        .start = @enumFromInt(extra[start + 1]),
        .end = @enumFromInt(extra[start + 2]),
    };
}

pub fn aggregateInitAt(extra: []const u32, at: ExtraIndex) []const Ref {
    const start = @intFromEnum(at);
    assert(start + 1 <= extra.len);
    return refsAt(extra, start + 1, extra[start]);
}

fn refsAt(extra: []const u32, start: u32, len: u32) []const Ref {
    assert(start + len <= extra.len);
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
    /// Where this came from, read against the owning `Func`'s module.
    node: AST.Node.Index,
    data: Data,

    pub const Index = Handle.Index("inst");

    pub const Data = union {
        none: void,
        un: Ref,
        bin: struct { lhs: Ref, rhs: Ref },
        field: struct { base: Ref, row: Compilation.Row.Index },
        /// The member asked about, or for `union_is` possibly a union of them.
        probe: struct { operand: Ref, member: Pool.Index },
        name: Pool.String,
        payload: ExtraIndex,
    };

    pub const Tag = enum(u8) {
        param,
        /// Produces the address. The name is `.empty` for a temporary.
        local,
        load,
        store,
        /// A field pointer, as mutable as its base.
        field_ptr,
        field_val,
        elem_ptr,
        /// Sign-widened then compared unsigned, so one test settles both edges.
        ///
        ///   written   widened to 64 bits    read as unsigned      verdict
        ///   i32   3   0x00000000_00000003                     3   3 < 4, passes
        ///   u64   3   0x00000000_00000003                     3   3 < 4, passes
        ///   i32  -1   0xffffffff_ffffffff  18446744073709551615   above 4, traps
        bounds_check,
        /// Traps unless the first is at most the second, widened as above.
        order_check,
        slice_len,
        slice_ptr,
        slice_make,
        /// A view of a count of elements at a pointer, on the caller's word alone.
        slice_from,

        add,
        sub,
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

        /// Traps where the negation does not fit, which is the type's lowest value.
        negate,
        not,
        bit_not,

        ptr_cast,
        int_from_ptr,
        widen,
        /// The value when the type holds it, the union's other member when not.
        int_cast,
        int_fits,

        union_init,
        /// Whether the union holds the member, or any of a union of them. Void for a branch.
        union_is,
        union_narrow,

        call,
        aggregate_init,

        /// Both enums list the binary operators in one order.
        pub fn ofBinary(op: AST.BinaryOp) Tag {
            assert(op != .bool_and);
            assert(op != .bool_or);
            return @enumFromInt(@intFromEnum(Tag.add) + @intFromEnum(op));
        }

        pub fn binaryOp(tag: Tag) AST.BinaryOp {
            assert(@intFromEnum(tag) >= @intFromEnum(Tag.add));
            assert(@intFromEnum(tag) <= @intFromEnum(Tag.cmp_ge));
            return @enumFromInt(@intFromEnum(tag) - @intFromEnum(Tag.add));
        }

        pub fn payload(tag: Tag) std.meta.FieldEnum(Data) {
            return switch (tag) {
                .param, .local => .name,
                .field_ptr, .field_val => .field,
                .union_is, .union_init => .probe,
                .call, .slice_make, .aggregate_init => .payload,
                .load, .slice_len, .slice_ptr, .negate, .not, .bit_not => .un,
                .ptr_cast, .int_from_ptr, .widen, .int_cast, .int_fits => .un,
                .union_narrow => .un,
                .store, .elem_ptr, .slice_from, .bounds_check, .order_check => .bin,
                .add, .sub, .mul, .div, .mod => .bin,
                .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => .bin,
                .cmp_eq, .cmp_ne, .cmp_lt, .cmp_le, .cmp_gt, .cmp_ge => .bin,
            };
        }
    };
};

pub const Block = struct {
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
            return @enumFromInt(raw);
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }
    };
};

pub const Terminator = union(enum) {
    jump: Block.Index,
    /// The then edge is taken when the union condition holds its first member.
    branch: struct { cond: Ref, then_block: Block.Index, else_block: Block.Index },
    ret: Ref,
    trap,
};

comptime {
    assert(@sizeOf(Inst.Tag) == 1);
    assert(@sizeOf(Ref) == 4);
    assert(@sizeOf(AST.Node.Index) == 4);
    if (std.debug.runtime_safety == false) assert(@sizeOf(Inst.Data) == 8);
    assert(@sizeOf(Block) <= 24);
    // the largest instruction ref stays one below `none`, never colliding
    assert(@intFromEnum(Ref.none) == Ref.inst_bit + Ref.inst_count_max);
    // the two ends pin the binary operators to their tags, so nothing slips in between
    assert(Inst.Tag.ofBinary(.add) == .add);
    assert(Inst.Tag.ofBinary(.greater_or_equal) == .cmp_ge);
    assert(Inst.Tag.binaryOp(.cmp_ge) == .greater_or_equal);
}
