const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Pool = @import("Pool.zig");

size: u32,
alignment: u32,

const Layout = @This();

/// 64-bit
pub const pointer_size = 8;

/// The tag is one byte, at the payload's end.
pub const tag_size = 1;

comptime {
    // a wider member cap needs a wider tag, so a change there must move both
    assert(Pool.union_members_max <= 1 << (8 * tag_size));
}

/// The most bytes a type may hold, which keeps every size a `u32`.
pub const size_max = std.math.maxInt(u32);

/// The lowest a negative index reads as once widened, the `i64` minimum.
const negative_floor = 1 << 63;

comptime {
    // `bounds_check` reads a negative index above every length, which needs this cap
    assert(size_max < negative_floor);
    // a stride is at least one byte, so a byte cap is also an element cap
    assert(@sizeOf(u8) == 1);
}

/// Far past any embedding chain the declaration limits admit.
const depth_max = 512;

comptime {
    // a chain costs one `ensure` per link, and a type nests no deeper than the parser allows
    assert(depth_max > Compilation.analyze_max + AST.nest_max);
}

pub const Result = union(enum) {
    layout: Layout,
    /// Something underneath was refused and already reported.
    poison,
    /// Past `size_max`. The caller reports where the size was asked.
    too_large,
};

pub fn of(
    comp: *Compilation,
    origin: Compilation.Origin,
    index: Pool.Index,
) Allocator.Error!Result {
    return ofBounded(comp, origin, index, 0);
}

fn ofBounded(
    comp: *Compilation,
    origin: Compilation.Origin,
    index: Pool.Index,
    depth: u32,
) Allocator.Error!Result {
    assert(depth < depth_max);
    if (comp.layouts.get(index)) |known| return .{ .layout = known };

    const result: Result = switch (comp.pool.keyOf(index)) {
        .type_simple => |simple| switch (simple) {
            .poison => .poison,
            .i8, .u8 => .{ .layout = .{ .size = 1, .alignment = 1 } },
            .i16, .u16 => .{ .layout = .{ .size = 2, .alignment = 2 } },
            .i32, .u32, .f32 => .{ .layout = .{ .size = 4, .alignment = 4 } },
            .i64, .u64, .f64 => .{ .layout = .{ .size = 8, .alignment = 8 } },
            // a written type is never void or untyped
            .void, .untyped_int, .untyped_float, .untyped_aggregate => unreachable,
        },
        .type_pointer => .{ .layout = .{
            .size = pointer_size,
            .alignment = pointer_size,
        } },
        // an address and a count, two words
        .type_slice => .{ .layout = .{
            .size = 2 * pointer_size,
            .alignment = pointer_size,
        } },
        .type_unit => .{ .layout = .{ .size = 0, .alignment = 1 } },
        .type_array => |array| try ofArray(comp, origin, array, depth),
        .type_struct => |instance| try ofStruct(comp, origin, instance, depth),
        .type_union => try ofUnion(comp, origin, index, depth),
        .value_int, .value_float, .value_aggregate => unreachable,
        .value_unit, .value_union, .value_slice => unreachable,
    };

    if (result == .layout) {
        assert(std.math.isPowerOfTwo(result.layout.alignment));
        assert(result.layout.size % result.layout.alignment == 0);
        try comp.layouts.put(comp.gpa, index, result.layout);
    }
    return result;
}

fn ofArray(
    comp: *Compilation,
    origin: Compilation.Origin,
    array: Pool.Key.Array,
    depth: u32,
) Allocator.Error!Result {
    const element = switch (try ofBounded(comp, origin, array.child, depth + 1)) {
        .layout => |found| found,
        .poison => return .poison,
        .too_large => return .too_large,
    };
    assert(element.size % element.alignment == 0);

    const total = std.math.mul(u64, array.len, element.size) catch return .too_large;
    if (total > size_max) return .too_large;
    return .{ .layout = .{ .size = @intCast(total), .alignment = element.alignment } };
}

fn ofStruct(
    comp: *Compilation,
    origin: Compilation.Origin,
    instance: Pool.Instance,
    depth: u32,
) Allocator.Error!Result {
    try comp.ensure(.of(.rows, instance), origin);
    // the embedding walk proved this terminates, which bounds the recursion
    try comp.ensure(.of(.embedding, instance), origin);
    if (comp.instanceAt(instance).rows_state != .done) return .poison;
    if (comp.instanceAt(instance).deep_state != .done) return .poison;

    var size: u64 = 0;
    var alignment: u32 = 1;
    const rows = comp.instanceAt(instance).rows;

    for (rows.start..rows.end()) |raw| {
        // by index, because a field's own layout can grow the rows table
        const row = comp.rowAt(.from(raw));
        const field = switch (try ofBounded(comp, origin, row.type, depth + 1)) {
            .layout => |found| found,
            .poison => return .poison,
            .too_large => return .too_large,
        };
        size = std.mem.alignForward(u64, size, field.alignment);
        size += field.size;
        if (size > size_max) return .too_large;
        alignment = @max(alignment, field.alignment);
    }

    // the size is the stride, rounded up so a row of them stays aligned
    const total = std.mem.alignForward(u64, size, alignment);
    if (total > size_max) return .too_large;
    return .{ .layout = .{ .size = @intCast(total), .alignment = alignment } };
}

/// A tag and a payload, or the zero niche.
fn ofUnion(
    comp: *Compilation,
    origin: Compilation.Origin,
    index: Pool.Index,
    depth: u32,
) Allocator.Error!Result {
    const pool = &comp.pool;
    const count = pool.unionMemberCount(index);
    assert(count >= 2);

    var payload_size: u32 = 0;
    var payload_alignment: u32 = 1;
    // the one member that could hide a tag in the address it carries
    var carrier: ?Layout = null;
    var units: u32 = 0;
    var at: u32 = 0;

    while (at < count) : (at += 1) {
        const member = pool.unionMemberAt(index, at);
        const found = switch (try ofBounded(comp, origin, member, depth + 1)) {
            .layout => |layout| layout,
            .poison => return .poison,
            .too_large => return .too_large,
        };
        payload_size = @max(payload_size, found.size);
        payload_alignment = @max(payload_alignment, found.alignment);
        switch (pool.keyOf(member)) {
            // a pointer and a view both lead with an address that is never zero
            .type_pointer, .type_slice => carrier = found,
            .type_unit => units += 1,
            else => {},
        }
    }

    // the zero niche. no address is zero, so one unit member hides there and no tag exists
    //
    //   *Node | none      0x00007f2e51c04150                        the *Node
    //                     0x0000000000000000                        none
    //   []u32 | none      0x00007f2e51c04150  0x0000000000000004    the []u32
    //                     0x0000000000000000  ------------------    none, count unread
    if (count == 2 and units == 1) {
        if (carrier) |only| return .{ .layout = only };
    }

    const total = std.mem.alignForward(
        u64,
        @as(u64, payload_size) + tag_size,
        payload_alignment,
    );
    if (total > size_max) return .too_large;
    return .{ .layout = .{
        .size = @intCast(total),
        .alignment = payload_alignment,
    } };
}
