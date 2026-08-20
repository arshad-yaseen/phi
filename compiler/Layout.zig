const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Pool = @import("Pool.zig");

size: u32,
alignment: u32,

const Layout = @This();

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

pub const depth_max = 512;

comptime {
    // a chain costs one `ensure` per link, and a type nests no deeper than the parser allows
    assert(depth_max > Compilation.analyze_max + AST.nest_max);
}

pub const Error = Allocator.Error || error{ Poison, TooLarge };

pub fn of(comp: *Compilation, origin: Compilation.Origin, index: Pool.Index) Error!Layout {
    return ofBounded(comp, origin, index, 0);
}

fn ofBounded(
    comp: *Compilation,
    origin: Compilation.Origin,
    index: Pool.Index,
    depth: u32,
) Error!Layout {
    assert(depth < depth_max);
    if (comp.layouts.get(index)) |known| return known;

    const found: Layout = switch (comp.pool.typeKey(index)) {
        .type_simple => |simple| switch (simple) {
            .poison => return error.Poison,
            .i8, .u8 => .{ .size = 1, .alignment = 1 },
            .i16, .u16 => .{ .size = 2, .alignment = 2 },
            .i32, .u32, .f32 => .{ .size = 4, .alignment = 4 },
            .i64, .u64, .f64 => .{ .size = 8, .alignment = 8 },
            // a written type is never void or untyped
            .void, .untyped_int, .untyped_float, .untyped_aggregate => unreachable,
        },
        .type_pointer => addressed(comp, 1),
        .type_slice => addressed(comp, 2),
        .type_unit => .{ .size = 0, .alignment = 1 },
        .type_array => |array| try ofArray(comp, origin, array, depth),
        .type_struct => |instance| try ofStruct(comp, origin, instance, depth),
        .type_union => try ofUnion(comp, origin, index, depth),
    };

    assert(std.math.isPowerOfTwo(found.alignment));
    assert(found.size % found.alignment == 0);
    try comp.layouts.put(comp.gpa, index, found);
    return found;
}

/// One address, or the two words a view lays end to end.
fn addressed(comp: *const Compilation, words: u32) Layout {
    const size = comp.target.pointerSize();
    return .{ .size = words * size, .alignment = size };
}

fn ofArray(
    comp: *Compilation,
    origin: Compilation.Origin,
    array: Pool.Key.Array,
    depth: u32,
) Error!Layout {
    const element = try ofBounded(comp, origin, array.child, depth + 1);
    assert(element.size % element.alignment == 0);

    const total = std.math.mul(u64, array.len, element.size) catch return error.TooLarge;
    return sized(total, element.alignment);
}

fn ofStruct(
    comp: *Compilation,
    origin: Compilation.Origin,
    instance: Pool.Instance,
    depth: u32,
) Error!Layout {
    try comp.ensure(.of(.rows, instance), origin);
    // the embedding walk proved this terminates, which bounds the recursion
    try comp.ensure(.of(.embedding, instance), origin);
    if (comp.instanceAt(instance).rows_state != .done) return error.Poison;
    if (comp.instanceAt(instance).deep_state != .done) return error.Poison;

    var size: u64 = 0;
    var alignment: u32 = 1;
    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        // by index, because a field's own layout can grow the rows table
        const row = comp.rowAt(.from(raw));
        const field = try ofBounded(comp, origin, row.type, depth + 1);
        size = std.mem.alignForward(u64, size, field.alignment) + field.size;
        if (size > size_max) return error.TooLarge;
        alignment = @max(alignment, field.alignment);
    }

    return sized(std.mem.alignForward(u64, size, alignment), alignment);
}

/// Two members where one is a bare unit. The unit takes the zero address and
/// the tag goes away.
///
///   *Node | none      0x00007f2e51c04150                        the *Node
///                     0x0000000000000000                        none
///   []u32 | none      0x00007f2e51c04150  0x0000000000000004    the []u32
///                     0x0000000000000000  ------------------    none, count unread
pub fn niche(pool: *const Pool, index: Pool.Index) ?Niche {
    if (pool.isUnion(index) == false) return null;
    if (pool.unionMemberCount(index) != 2) return null;

    const first = pool.unionMemberAt(index, 0);
    const second = pool.unionMemberAt(index, 1);
    if (pool.keyOf(first) == .type_unit) return carrierOf(pool, second);
    if (pool.keyOf(second) == .type_unit) return carrierOf(pool, first);
    return null;
}

/// The member that keeps the address, and whether a view, whose count goes unread.
pub const Niche = struct { member: Pool.Index, form: enum { pointer, slice } };

fn carrierOf(pool: *const Pool, index: Pool.Index) ?Niche {
    return switch (pool.keyOf(index)) {
        .type_pointer => .{ .member = index, .form = .pointer },
        .type_slice => .{ .member = index, .form = .slice },
        else => null,
    };
}

fn ofUnion(
    comp: *Compilation,
    origin: Compilation.Origin,
    index: Pool.Index,
    depth: u32,
) Error!Layout {
    const pool = &comp.pool;
    assert(pool.unionMemberCount(index) >= 2);
    if (niche(pool, index)) |it| return ofBounded(comp, origin, it.member, depth + 1);

    var payload_size: u32 = 0;
    var payload_alignment: u32 = 1;
    var members = pool.membersOf(index);
    while (members.next()) |member| {
        const found = try ofBounded(comp, origin, member, depth + 1);
        payload_size = @max(payload_size, found.size);
        payload_alignment = @max(payload_alignment, found.alignment);
    }

    return sized(@as(u64, payload_size) + tag_size, payload_alignment);
}

fn sized(size: u64, alignment: u32) Error!Layout {
    const total = std.mem.alignForward(u64, size, alignment);
    if (total > size_max) return error.TooLarge;
    return .{ .size = @intCast(total), .alignment = alignment };
}
