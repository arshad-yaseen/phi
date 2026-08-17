//! One item per type and per payload, so equality is index equality.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Handle = @import("Handle.zig");
const Module = @import("Module.zig");

items: std.MultiArrayList(Item),
/// Wide payloads, each a type and its value words.
extra: std.ArrayList(u32),
/// Every interned string, null terminated.
bytes: std.ArrayList(u8),
/// Item lookup, so one (tag, payload) is one index forever.
map: std.HashMapUnmanaged(Index, void, IndexContext, load_percentage),
string_map: std.HashMapUnmanaged(String, void, StringContext, load_percentage),
/// Marked and restored. Gathers indexes a walk holds on to, which nests.
scratch: std.ArrayList(Index),
/// Small integer constants, so they skip the map. `.poison`, never a value, marks unfilled.
small_ints: [statics * small_int_range]Index,

const small_int_range = 256;

const load_percentage = std.hash_map.default_max_load_percentage;

const Pool = @This();

/// Interned before any source is read.
const statics = @typeInfo(SimpleType).@"enum".fields.len;

/// A type or a constant. `init` interns the named items in this order.
pub const Index = enum(u32) {
    /// A broken type and a broken value, which stays silent.
    poison,
    i8_type,
    i16_type,
    i32_type,
    i64_type,
    u8_type,
    u16_type,
    u32_type,
    u64_type,
    f32_type,
    f64_type,
    /// What a function with no return type returns.
    void_type,
    /// A number that has not met a type yet.
    untyped_int_type,
    untyped_float_type,
    /// A written `[a, b, c]`, which has not met a type yet.
    untyped_aggregate_type,
    _,

    pub fn from(raw: usize) Index {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(@as(u32, @intCast(raw)));
    }

    pub fn int(index: Index) u32 {
        return @intFromEnum(index);
    }
};

/// A struct instantiation. The rows live on `Compilation`.
pub const Instance = Handle.Index("instance");
pub const OptionalInstance = Instance.Optional;

/// An offset into `bytes`. The text runs to the next zero byte.
pub const String = enum(u32) {
    empty = 0,
    _,

    pub fn from(raw: usize) String {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(@as(u32, @intCast(raw)));
    }

    pub fn int(index: String) u32 {
        return @intFromEnum(index);
    }
};

/// A type with no payload, pinned to the static item it occupies.
pub const SimpleType = enum(u32) {
    poison = @intFromEnum(Index.poison),
    i8 = @intFromEnum(Index.i8_type),
    i16 = @intFromEnum(Index.i16_type),
    i32 = @intFromEnum(Index.i32_type),
    i64 = @intFromEnum(Index.i64_type),
    u8 = @intFromEnum(Index.u8_type),
    u16 = @intFromEnum(Index.u16_type),
    u32 = @intFromEnum(Index.u32_type),
    u64 = @intFromEnum(Index.u64_type),
    f32 = @intFromEnum(Index.f32_type),
    f64 = @intFromEnum(Index.f64_type),
    void = @intFromEnum(Index.void_type),
    untyped_int = @intFromEnum(Index.untyped_int_type),
    untyped_float = @intFromEnum(Index.untyped_float_type),
    untyped_aggregate = @intFromEnum(Index.untyped_aggregate_type),

    pub fn index(simple: SimpleType) Index {
        return @enumFromInt(@intFromEnum(simple));
    }

    /// Whether source may write this name.
    fn isSpellable(simple: SimpleType) bool {
        return switch (simple) {
            .i8, .i16, .i32, .i64 => true,
            .u8, .u16, .u32, .u64 => true,
            .f32, .f64 => true,
            .poison, .void => false,
            .untyped_int, .untyped_float, .untyped_aggregate => false,
        };
    }
};

// the primitive types

/// The type a name means in every file, read off the static items.
pub fn primitiveType(text: []const u8) ?Index {
    return primitives.get(text);
}

/// For a suggestion when a name is missed.
pub const primitive_names = primitives.keys();

/// Whether an interned string spells a primitive name, which `init` interns first.
pub fn isPrimitiveName(name: String) bool {
    if (name == .empty) return false;
    return name.int() < primitive_bytes_end;
}

/// Offset zero is the empty string, then the primitive names back to back.
const primitive_bytes_end = blk: {
    var total: u32 = 1;
    for (primitive_names) |name| total += name.len + 1;
    break :blk total;
};

const primitives = build: {
    const simples = std.enums.values(SimpleType);
    var entries: [simples.len]struct { []const u8, Index } = undefined;
    var count: usize = 0;
    for (simples) |simple| {
        if (simple.isSpellable() == false) continue;
        entries[count] = .{ @tagName(simple), simple.index() };
        count += 1;
    }
    break :build std.StaticStringMap(Index).initComptime(entries[0..count].*);
};

/// What one item means, spelled like the tag it is stored under.
pub const Key = union(enum) {
    type_simple: SimpleType,
    type_pointer: Pointer,
    /// N values of one type, contiguous. The length is part of the type.
    type_array: Array,
    /// A pointer and a length.
    type_slice: Slice,
    /// A nominal struct, whose identity is the instantiation.
    type_struct: Instance,
    /// A nominal unit type. Never generic, so the declaration is the identity.
    type_unit: Module.Decl.Index,
    /// Ordered distinct members, none a union. Borrowed from `extra`, stale at the next intern.
    type_union: []const Index,

    value_int: Int,
    value_float: Float,
    /// Ordered elements. Borrowed from `extra`, stale at the next intern.
    value_aggregate: Aggregate,
    /// The unit type, whose one value this is.
    value_unit: Index,
    /// A constant that knows its union. The union, then the member constant.
    value_union: Wrapped,
    /// A view of bytes the program owns, which is what a constant becomes on a `[]T`.
    value_slice: Viewed,
    /// An array whose every element is the same, held once. The length is in the type.
    value_splat: Splat,

    pub const Pointer = struct { child: Index, mutable: bool };
    /// A length no layout can hold is refused where the size is asked, not here.
    pub const Array = struct { child: Index, len: u64 };
    pub const Slice = struct { child: Index, mutable: bool };
    pub const Int = struct { type: Index, value: i128 };
    pub const Float = struct { type: Index, value: f64 };
    pub const Wrapped = struct { type: Index, value: Index };
    /// The view's own type, and the array constant holding the bytes it views.
    pub const Viewed = struct { type: Index, data: Index };
    pub const Splat = struct { type: Index, element: Index };
    pub const Aggregate = struct { type: Index, elems: []const Index };

    fn hash(key: Key) u64 {
        var hasher: std.hash.Wyhash = .init(@intFromEnum(std.meta.activeTag(key)));
        switch (key) {
            .type_union => |members| hasher.update(std.mem.sliceAsBytes(members)),
            .value_aggregate => |it| {
                std.hash.autoHash(&hasher, it.type);
                hasher.update(std.mem.sliceAsBytes(it.elems));
            },
            // by bits, because floats have no hash of their own
            .value_float => |it| {
                std.hash.autoHash(&hasher, it.type);
                std.hash.autoHash(&hasher, @as(u64, @bitCast(it.value)));
            },
            inline else => |payload| std.hash.autoHash(&hasher, payload),
        }
        return hasher.final();
    }

    fn eql(key: Key, other: Key) bool {
        if (std.meta.activeTag(key) != std.meta.activeTag(other)) return false;
        return switch (key) {
            .type_union => |members| std.mem.eql(Index, members, other.type_union),
            .value_aggregate => |it| it.type == other.value_aggregate.type and
                std.mem.eql(Index, it.elems, other.value_aggregate.elems),
            // by bits, so float equality is never asked
            .value_float => |it| it.type == other.value_float.type and
                @as(u64, @bitCast(it.value)) == @as(u64, @bitCast(other.value_float.value)),
            inline else => |payload, tag| std.meta.eql(payload, @field(other, @tagName(tag))),
        };
    }
};

const Item = struct {
    tag: Tag,
    data: u32,

    const Tag = enum(u8) {
        type_simple,
        type_pointer,
        type_pointer_var,
        /// `data` points at `extra`. The element type, then the length in two words.
        type_array,
        /// `data` is the element type, the way a pointer stores its child.
        type_slice,
        type_slice_var,
        type_struct,
        type_unit,
        /// `data` points at `extra`. The member count, then the members.
        type_union,
        /// `data` points at `extra`.
        value_int,
        /// `data` points at `extra`.
        value_float,
        /// `data` points at `extra`. The type, the element count, then the elements.
        value_aggregate,
        /// `data` is its unit type.
        value_unit,
        /// `data` points at `extra`. The union, then the member constant.
        value_union,
        /// `data` points at `extra`. The view type, then the array it views.
        value_slice,
        /// `data` points at `extra`. The array type, then the one element.
        value_splat,
    };
};

comptime {
    assert(@sizeOf(Item.Tag) == 1);
    // the stated fold width is the stored width
    assert(fold_bits == @bitSizeOf(i128));
    // every integer a program can write folds without truncating
    assert(@bitSizeOf(u64) < fold_bits);
    assert(@bitSizeOf(i64) < fold_bits);
}

pub fn init(pool: *Pool, gpa: Allocator) Allocator.Error!void {
    pool.* = .{
        .items = .empty,
        .extra = .empty,
        .bytes = .empty,
        .map = .empty,
        .string_map = .empty,
        .scratch = .empty,
        .small_ints = @splat(.poison),
    };
    errdefer pool.deinit(gpa);

    // a few hundred items per source file
    try pool.items.ensureTotalCapacity(gpa, 256);
    try pool.bytes.ensureTotalCapacity(gpa, 1024);

    // offset zero is the empty string, so `String.empty` needs no lookup
    pool.bytes.appendAssumeCapacity(0);

    for (std.enums.values(SimpleType)) |simple| {
        const index = try pool.intern(gpa, .{ .type_simple = simple });
        assert(index == simple.index());
    }
    assert(pool.items.len == statics);

    // primitive names first, so `isPrimitiveName` is one offset test
    for (primitive_names) |name| _ = try pool.string(gpa, name);
    assert(pool.bytes.items.len == primitive_bytes_end);
}

pub fn deinit(pool: *Pool, gpa: Allocator) void {
    pool.items.deinit(gpa);
    pool.extra.deinit(gpa);
    pool.bytes.deinit(gpa);
    pool.map.deinit(gpa);
    pool.string_map.deinit(gpa);
    pool.scratch.deinit(gpa);
    pool.* = undefined;
}

// interning

pub fn intern(pool: *Pool, gpa: Allocator, key: Key) Allocator.Error!Index {
    const small = smallIntSlot(key);
    if (small) |at| {
        if (pool.small_ints[at] != .poison) return pool.small_ints[at];
    }

    const gop = try pool.map.getOrPutContextAdapted(
        gpa,
        key,
        KeyAdapter{ .pool = pool },
        IndexContext{ .pool = pool },
    );
    if (gop.found_existing) return gop.key_ptr.*;

    if (pool.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    const index: Index = .from(pool.items.len);

    const item: Item = switch (key) {
        .type_simple => |simple| .{ .tag = .type_simple, .data = @intFromEnum(simple) },
        .type_pointer => |pointer| .{
            .tag = if (pointer.mutable) .type_pointer_var else .type_pointer,
            .data = pointer.child.int(),
        },
        .type_array => |array| item: {
            assert(pool.isType(array.child));
            break :item .{
                .tag = .type_array,
                .data = try pool.addExtra(gpa, &.{array.child.int()}, &wordsOf(array.len)),
            };
        },
        .type_slice => |slice| item: {
            assert(pool.isType(slice.child));
            break :item .{
                .tag = if (slice.mutable) .type_slice_var else .type_slice,
                .data = slice.child.int(),
            };
        },
        .type_struct => |instance| .{ .tag = .type_struct, .data = instance.int() },
        .type_unit => |decl| .{ .tag = .type_unit, .data = decl.int() },
        .type_union => |members| item: {
            assert(members.len >= 2);
            assert(members.len <= union_members_max);
            for (members) |member| assert(pool.isUnion(member) == false);
            for (members, 0..) |member, at| {
                assert(pool.isType(member));
                for (members[0..at]) |earlier| assert(member != earlier);
            }
            break :item .{
                .tag = .type_union,
                .data = try pool.addExtra(gpa, &.{@intCast(members.len)}, @ptrCast(members)),
            };
        },
        .value_union => |it| item: {
            assert(pool.isUnion(it.type));
            assert(pool.isType(it.value) == false);
            assert(pool.keyOf(it.value) != .value_union);
            assert(pool.unionHas(it.type, pool.typeOfValue(it.value)));
            break :item .{
                .tag = .value_union,
                .data = try pool.addExtra(gpa, &.{it.type.int()}, &.{it.value.int()}),
            };
        },
        .value_slice => |it| item: {
            assert(pool.keyOf(it.type) == .type_slice);
            // the bytes are an array constant, so the view has a length and a layout
            assert(pool.keyOf(pool.typeOfValue(it.data)) == .type_array);
            break :item .{
                .tag = .value_slice,
                .data = try pool.addExtra(gpa, &.{it.type.int()}, &.{it.data.int()}),
            };
        },
        .value_splat => |it| item: {
            assert(pool.keyOf(it.type) == .type_array);
            assert(pool.isType(it.element) == false);
            break :item .{
                .tag = .value_splat,
                .data = try pool.addExtra(gpa, &.{it.type.int()}, &.{it.element.int()}),
            };
        },
        .value_aggregate => |it| item: {
            assert(pool.isType(it.type));
            for (it.elems) |element| assert(pool.isType(element) == false);
            break :item .{
                .tag = .value_aggregate,
                .data = try pool.addExtra(
                    gpa,
                    &.{ it.type.int(), @intCast(it.elems.len) },
                    @ptrCast(it.elems),
                ),
            };
        },
        .value_unit => |unit_type| item: {
            assert(pool.items.items(.tag)[unit_type.int()] == .type_unit);
            break :item .{ .tag = .value_unit, .data = unit_type.int() };
        },
        .value_int => |it| .{
            .tag = .value_int,
            .data = try pool.addExtra(gpa, &.{it.type.int()}, &wordsOf(it.value)),
        },
        .value_float => |it| .{
            .tag = .value_float,
            .data = try pool.addExtra(gpa, &.{it.type.int()}, &wordsOf(@as(u64, @bitCast(it.value)))),
        },
    };
    try pool.items.append(gpa, item);
    gop.key_ptr.* = index;
    if (small) |at| pool.small_ints[at] = index;

    assert(pool.items.len == index.int() + 1);
    assert(key.eql(pool.keyOf(index)));
    return index;
}

fn smallIntSlot(key: Key) ?u32 {
    if (key != .value_int) return null;
    const it = key.value_int;
    if (it.type.int() >= statics) return null;
    if (it.value < 0) return null;
    if (it.value >= small_int_range) return null;
    const slot = it.type.int() * small_int_range + @as(u32, @intCast(it.value));
    assert(slot < statics * small_int_range);
    return slot;
}

pub fn keyOf(pool: *const Pool, index: Index) Key {
    assert(index.int() < pool.items.len);

    const data = pool.items.items(.data)[index.int()];
    return switch (pool.items.items(.tag)[index.int()]) {
        .type_simple => .{ .type_simple = @enumFromInt(data) },
        .type_pointer => .{ .type_pointer = .{ .child = @enumFromInt(data), .mutable = false } },
        .type_pointer_var => .{ .type_pointer = .{ .child = @enumFromInt(data), .mutable = true } },
        .type_array => .{ .type_array = .{
            .child = @enumFromInt(pool.extra.items[data]),
            .len = @bitCast(pool.extraWords(data + 1, 2).*),
        } },
        .type_slice => .{ .type_slice = .{ .child = @enumFromInt(data), .mutable = false } },
        .type_slice_var => .{ .type_slice = .{ .child = @enumFromInt(data), .mutable = true } },
        .type_struct => .{ .type_struct = @enumFromInt(data) },
        .type_unit => .{ .type_unit = @enumFromInt(data) },
        .type_union => .{ .type_union = pool.unionMembers(index) },
        .value_aggregate => .{ .value_aggregate = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .elems = @ptrCast(pool.extra.items[data + 2 ..][0..pool.extra.items[data + 1]]),
        } },
        .value_unit => .{ .value_unit = @enumFromInt(data) },
        .value_union => .{ .value_union = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .value = @enumFromInt(pool.extra.items[data + 1]),
        } },
        .value_slice => .{ .value_slice = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .data = @enumFromInt(pool.extra.items[data + 1]),
        } },
        .value_splat => .{ .value_splat = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .element = @enumFromInt(pool.extra.items[data + 1]),
        } },
        .value_int => .{ .value_int = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .value = @bitCast(pool.extraWords(data + 1, 4).*),
        } },
        .value_float => .{ .value_float = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .value = @bitCast(@as(u64, @bitCast(pool.extraWords(data + 1, 2).*))),
        } },
    };
}

/// The most members one union may hold, after flattening.
pub const union_members_max = 255;

/// Everything except `index` is a mistake, reported where the union is written.
pub const Unite = union(enum) {
    index: Index,
    /// Already in the flattened list. An alias is not a new type.
    duplicate: Index,
    too_wide,
};

/// The one way a union is built. Members splice in flat, and a repeat is refused.
pub fn unite(pool: *Pool, gpa: Allocator, members: []const Index) Allocator.Error!Unite {
    assert(members.len >= 2);

    for (members) |member| {
        if (member == .poison) return .{ .index = .poison };
        assert(pool.isType(member));
    }

    var flat: [union_members_max]Index = undefined;
    var count: u32 = 0;
    for (members) |member| {
        switch (pool.keyOf(member)) {
            // an interned union is already flat, so one splice stays flat
            .type_union => |splice| {
                if (count + splice.len > union_members_max) return .too_wide;
                @memcpy(flat[count..][0..splice.len], splice);
                count += @intCast(splice.len);
            },
            else => {
                if (count == union_members_max) return .too_wide;
                flat[count] = member;
                count += 1;
            },
        }
    }
    assert(count >= members.len);

    for (flat[0..count], 0..) |member, at| {
        for (flat[0..at]) |earlier| {
            if (member == earlier) return .{ .duplicate = member };
        }
    }
    return .{ .index = try pool.intern(gpa, .{ .type_union = flat[0..count] }) };
}

pub fn isUnion(pool: *const Pool, index: Index) bool {
    assert(index.int() < pool.items.len);
    return pool.items.items(.tag)[index.int()] == .type_union;
}

pub fn unionHas(pool: *const Pool, union_index: Index, member: Index) bool {
    return pool.unionMemberPosition(union_index, member) != null;
}

pub fn unionMemberPosition(pool: *const Pool, union_index: Index, member: Index) ?u32 {
    if (pool.isUnion(member)) return null;
    for (pool.unionMembers(union_index), 0..) |candidate, at| {
        if (candidate == member) return @intCast(at);
    }
    return null;
}

/// Whether `member` is `set` itself, or one of its members where `set` is a
/// union. A member is never a union, so the two never both hold.
pub fn covers(pool: *const Pool, set: Index, member: Index) bool {
    if (set == member) return true;
    return pool.isUnion(set) and pool.unionHas(set, member);
}

/// The union without `removed`, one member or a union of them. The rest as a
/// union, the one member left, or null where nothing is left.
pub fn unionWithout(
    pool: *Pool,
    gpa: Allocator,
    union_index: Index,
    removed: Index,
) Allocator.Error!?Index {
    var flat: [union_members_max]Index = undefined;
    var count: u32 = 0;
    for (pool.unionMembers(union_index)) |candidate| {
        if (pool.covers(removed, candidate)) continue;
        flat[count] = candidate;
        count += 1;
    }
    assert(count < pool.unionMemberCount(union_index));

    if (count == 0) return null;
    if (count == 1) return flat[0];
    return try pool.intern(gpa, .{ .type_union = flat[0..count] });
}

/// Whether `wide` lists every member of `narrow`, one type or a union. Membership, not order.
pub fn unionCovers(pool: *const Pool, wide: Index, narrow: Index) bool {
    assert(pool.isUnion(wide));
    if (pool.isUnion(narrow) == false) return pool.unionHas(wide, narrow);
    for (pool.unionMembers(narrow)) |member| {
        if (pool.unionHas(wide, member) == false) return false;
    }
    return true;
}

/// Borrowed from `extra`, stale at the next intern. A walk that interns reads
/// by position through `unionMemberCount` and `unionMemberAt` instead.
pub fn unionMembers(pool: *const Pool, index: Index) []const Index {
    assert(pool.isUnion(index));
    const data = pool.items.items(.data)[index.int()];
    return @ptrCast(pool.extra.items[data + 1 ..][0..pool.extra.items[data]]);
}

pub fn unionMemberCount(pool: *const Pool, index: Index) u32 {
    return @intCast(pool.unionMembers(index).len);
}

pub fn unionMemberAt(pool: *const Pool, index: Index, at: u32) Index {
    return pool.unionMembers(index)[at];
}

/// What a type leads with, which a union answers with its first member and every
/// other type with itself.
pub fn firstMember(pool: *const Pool, index: Index) Index {
    if (pool.isUnion(index) == false) return index;
    return pool.unionMemberAt(index, 0);
}

pub fn string(pool: *Pool, gpa: Allocator, text: []const u8) Allocator.Error!String {
    // guarded, because a scanning assert survives into release builds
    if (std.debug.runtime_safety) assert(std.mem.indexOfScalar(u8, text, 0) == null);

    const gop = try pool.string_map.getOrPutContextAdapted(
        gpa,
        text,
        StringAdapter{ .bytes = &pool.bytes },
        StringContext{ .bytes = &pool.bytes },
    );
    if (gop.found_existing) return gop.key_ptr.*;

    if (pool.bytes.items.len + text.len + 1 > std.math.maxInt(u32)) return error.OutOfMemory;
    const offset: String = .from(pool.bytes.items.len);

    try pool.bytes.ensureUnusedCapacity(gpa, text.len + 1);
    pool.bytes.appendSliceAssumeCapacity(text);
    pool.bytes.appendAssumeCapacity(0);
    gop.key_ptr.* = offset;

    assert(std.mem.eql(u8, pool.stringText(offset), text));
    return offset;
}

pub fn sameText(pool: *const Pool, name: String, text: []const u8) bool {
    assert(name.int() < pool.bytes.items.len);
    // guarded, because a scanning assert survives into release builds
    if (std.debug.runtime_safety) assert(std.mem.indexOfScalar(u8, text, 0) == null);
    return spells(pool.bytes.items, name, text);
}

/// Interning zero-terminates, so a longer `text` mismatches on the zero.
fn spells(bytes: []const u8, name: String, text: []const u8) bool {
    const stored = bytes[name.int()..];
    for (text, 0..) |byte, at| {
        if (stored[at] != byte) return false;
    }
    return stored[text.len] == 0;
}

pub fn stringText(pool: *const Pool, index: String) [:0]const u8 {
    assert(index.int() < pool.bytes.items.len);
    const base = pool.bytes.items[index.int()..];
    // interning terminates every string, so the zero byte is always found
    const length = std.mem.indexOfScalar(u8, base, 0).?;
    return base[0..length :0];
}

// questions every stage asks

/// Only a value has one. `poison` is both, and answers with itself.
pub fn typeOfValue(pool: *const Pool, value: Index) Index {
    return switch (pool.keyOf(value)) {
        .value_int => |it| it.type,
        .value_float => |it| it.type,
        .value_aggregate => |it| it.type,
        .value_unit => |unit_type| unit_type,
        .value_union => |it| it.type,
        .value_slice => |it| it.type,
        .value_splat => |it| it.type,
        .type_simple => |simple| simple: {
            assert(simple == .poison);
            break :simple .poison;
        },
        .type_pointer, .type_array, .type_slice => unreachable,
        .type_struct, .type_unit, .type_union => unreachable,
    };
}

pub fn isType(pool: *const Pool, index: Index) bool {
    return switch (pool.keyOf(index)) {
        .type_simple, .type_pointer, .type_array, .type_slice => true,
        .type_struct, .type_unit, .type_union => true,
        .value_int, .value_float, .value_aggregate => false,
        .value_unit, .value_union, .value_slice, .value_splat => false,
    };
}

/// With `aggregateAt`, for walks that intern. `keyOf` only borrows.
pub fn aggregateLen(pool: *const Pool, index: Index) u64 {
    const data = pool.items.items(.data)[index.int()];
    return switch (pool.items.items(.tag)[index.int()]) {
        .value_aggregate => pool.extra.items[data + 1],
        .value_splat => pool.keyOf(@enumFromInt(pool.extra.items[data])).type_array.len,
        else => unreachable,
    };
}

pub fn aggregateAt(pool: *const Pool, index: Index, at: u64) Index {
    assert(at < pool.aggregateLen(index));
    const data = pool.items.items(.data)[index.int()];
    return switch (pool.items.items(.tag)[index.int()]) {
        .value_aggregate => @enumFromInt(pool.extra.items[data + 2 + at]),
        .value_splat => @enumFromInt(pool.extra.items[data + 1]),
        else => unreachable,
    };
}

pub fn isInteger(index: Index) bool {
    return switch (index) {
        .i8_type, .i16_type, .i32_type, .i64_type => true,
        .u8_type, .u16_type, .u32_type, .u64_type => true,
        .untyped_int_type => true,
        else => false,
    };
}

pub fn isFloat(index: Index) bool {
    return switch (index) {
        .f32_type, .f64_type, .untyped_float_type => true,
        else => false,
    };
}

/// A constant that has not met a type yet, so it may still take one.
pub fn isUntyped(index: Index) bool {
    if (index == .untyped_int_type) return true;
    if (index == .untyped_float_type) return true;
    return index == .untyped_aggregate_type;
}

pub fn isNumeric(index: Index) bool {
    if (isInteger(index)) return true;
    return isFloat(index);
}

pub fn isSizedInt(index: Index) bool {
    if (isInteger(index) == false) return false;
    return index != .untyped_int_type;
}

/// Whether every value of `from` is also a value of `into`, so no value is lost.
pub fn widens(from: Index, into: Index) bool {
    if (from == .f32_type) return into == .f64_type;
    if (isSizedInt(from) == false) return false;
    if (isSizedFloat(into)) {
        // a float holds every integer up to its mantissa exactly, and nothing wider
        return minInt(from) >= -exactIntMax(into) and maxInt(from) <= exactIntMax(into);
    }
    if (isSizedInt(into) == false) return false;
    if (minInt(into) > minInt(from)) return false;
    return maxInt(from) <= maxInt(into);
}

fn isSizedFloat(index: Index) bool {
    return index == .f32_type or index == .f64_type;
}

/// The largest integer a float holds exactly, and every one below it.
fn exactIntMax(float_type: Index) i128 {
    return switch (float_type) {
        .f32_type => 1 << 24,
        .f64_type => 1 << 53,
        else => unreachable,
    };
}

/// The float that is exactly `value`, or null where the type would round it.
fn exactFloat(value: i128, type_index: Index) ?f64 {
    assert(isFloat(type_index));
    const wide = narrowFloat(@floatFromInt(value), type_index);
    // past the fold's own width nothing is exact, and reading back would overflow
    if (wide < -0x1p127 or wide >= 0x1p127) return null;
    if (@as(i128, @intFromFloat(wide)) != value) return null;
    return wide;
}

fn isSignedInt(index: Index) bool {
    return switch (index) {
        .i8_type, .i16_type, .i32_type, .i64_type => true,
        else => false,
    };
}

/// The lowest value an integer type holds. Exact, because every width folds in 128 bits.
pub fn minInt(type_index: Index) i128 {
    assert(isSizedInt(type_index));
    if (isSignedInt(type_index) == false) return 0;
    return -(@as(i128, 1) << @intCast(widthOf(type_index) - 1));
}

pub fn maxInt(type_index: Index) i128 {
    assert(isSizedInt(type_index));
    const value_bits = widthOf(type_index) - @intFromBool(isSignedInt(type_index));
    return (@as(i128, 1) << @intCast(value_bits)) - 1;
}

comptime {
    // both edges of every width sit inside the fold, which is what keeps them exact
    assert(std.math.maxInt(u64) < std.math.maxInt(i128));
    assert(std.math.minInt(i64) > std.math.minInt(i128));
}

pub fn fitsInt(value: i128, type_index: Index) bool {
    assert(isInteger(type_index) or isFloat(type_index));
    // untyped always fits, and every i128 is below the smallest float infinity
    if (isSizedInt(type_index) == false) return true;
    if (value < minInt(type_index)) return false;
    return value <= maxInt(type_index);
}

// the constant-folding core

/// Everything except `value` is a mistake, reported at the operator.
pub const Fold = union(enum) {
    value: Index,
    /// Past the 128 bits constants fold in.
    overflow,
    division_by_zero,
    /// Outside the width the shifted value occupies.
    bad_shift: struct { count: i128, type: Index },
    /// Refused by the type both operands carry.
    does_not_fit: struct { value: Index, type: Index },
    mismatch: struct { left: Index, right: Index },
    bad_operand: Index,
    /// A comparison's answer, spelled by the checker, because `bool` is declared.
    truth: bool,
};

/// The width constants fold in, which bounds every shift.
pub const fold_bits = 128;

pub fn fold(
    pool: *Pool,
    gpa: Allocator,
    op: AST.BinaryOp,
    lhs: Index,
    rhs: Index,
) Allocator.Error!Fold {
    if (lhs == .poison) return .{ .value = .poison };
    if (rhs == .poison) return .{ .value = .poison };

    assert(op != .bool_and);
    assert(op != .bool_or);

    const left = numberOf(pool.keyOf(lhs)) orelse return .{ .bad_operand = pool.typeOfValue(lhs) };
    const right = numberOf(pool.keyOf(rhs)) orelse return .{ .bad_operand = pool.typeOfValue(rhs) };

    const result_type = sharedType(left.type, right.type) orelse {
        return .{ .mismatch = .{ .left = left.type, .right = right.type } };
    };

    // both meet the shared type first, so a constant that would round is refused as at run time
    const a = try pool.fitNumber(gpa, lhs, result_type) orelse {
        return .{ .does_not_fit = .{ .value = lhs, .type = result_type } };
    };
    const b = try pool.fitNumber(gpa, rhs, result_type) orelse {
        return .{ .does_not_fit = .{ .value = rhs, .type = result_type } };
    };

    if (isFloat(result_type)) {
        if (compareFold(op, a.float, b.float)) |answer| return answer;
        return pool.foldFloat(gpa, op, a.float, b.float, result_type);
    }
    if (compareFold(op, a.int, b.int)) |answer| return answer;
    return pool.foldInt(gpa, op, a.int, b.int, result_type);
}

/// A number as the type holds it, or null where it does not fit.
fn fitNumber(pool: *Pool, gpa: Allocator, value: Index, type_index: Index) Allocator.Error!?Number {
    return switch (try pool.fit(gpa, value, type_index, .allowed)) {
        // a number fitted to a numeric type is a number
        .value => |fitted| numberOf(pool.keyOf(fitted)).?,
        .does_not_fit => null,
        // `sharedType` admits only numeric pairs, so the kind always matches
        .wrong_kind => unreachable,
    };
}

/// The one place an operator becomes a comparison, so both widths ask it alike.
fn compareFold(op: AST.BinaryOp, a: anytype, b: @TypeOf(a)) ?Fold {
    return .{ .truth = switch (op) {
        .equal => a == b,
        .not_equal => a != b,
        .less_than => a < b,
        .less_or_equal => a <= b,
        .greater_than => a > b,
        .greater_or_equal => a >= b,
        else => return null,
    } };
}

pub fn foldNegate(pool: *Pool, gpa: Allocator, operand: Index) Allocator.Error!Fold {
    if (operand == .poison) return .{ .value = .poison };

    const number = numberOf(pool.keyOf(operand)) orelse {
        return .{ .bad_operand = pool.typeOfValue(operand) };
    };
    if (isFloat(number.type)) {
        return pool.internFloat(gpa, -number.float, number.type);
    }
    const negated = std.math.negate(number.int) catch return .overflow;
    return pool.internInt(gpa, negated, number.type);
}

/// The complement inside the operand's own type.
pub fn foldBitNot(pool: *Pool, gpa: Allocator, operand: Index) Allocator.Error!Fold {
    if (operand == .poison) return .{ .value = .poison };

    const number = numberOf(pool.keyOf(operand)) orelse {
        return .{ .bad_operand = pool.typeOfValue(operand) };
    };
    if (isInteger(number.type) == false) return .{ .bad_operand = number.type };
    return pool.internInt(gpa, complementOf(number.int, number.type), number.type);
}

/// The bits a value of this type occupies, which bounds every shift of it.
pub fn widthOf(type_index: Index) u16 {
    assert(isInteger(type_index));
    return switch (type_index) {
        .i8_type, .u8_type => 8,
        .i16_type, .u16_type => 16,
        .i32_type, .u32_type => 32,
        .i64_type, .u64_type => 64,
        .untyped_int_type => fold_bits,
        else => unreachable,
    };
}

/// Unsigned complements inside the width, everything else in two's complement.
fn complementOf(value: i128, type_index: Index) i128 {
    assert(isInteger(type_index));
    assert(fitsInt(value, type_index));

    if (isSignedInt(type_index) or type_index == .untyped_int_type) return ~value;
    return ~value & ((@as(i128, 1) << @intCast(widthOf(type_index))) - 1);
}

/// Null where the distance is not one the value's own width allows.
fn shiftAmount(count: i128, type_index: Index) ?std.math.Log2Int(i128) {
    if (count < 0) return null;
    if (count >= widthOf(type_index)) return null;
    return @intCast(count);
}

pub const Fit = union(enum) {
    value: Index,
    /// Right in kind, wrong in size.
    does_not_fit,
    wrong_kind,
};

/// Whether a settled constant may widen on the way in. An element never does.
pub const Widen = enum { allowed, refused };

/// An untyped constant meets any type its value fits, a settled one its own or wider.
pub fn fit(
    pool: *Pool,
    gpa: Allocator,
    value: Index,
    type_index: Index,
    widen: Widen,
) Allocator.Error!Fit {
    if (value == .poison) return .{ .value = .poison };
    if (type_index == .poison) return .{ .value = .poison };
    assert(pool.isType(type_index));

    // the first fitting member decides, read by position because fitting interns
    if (pool.isUnion(type_index)) {
        const count = pool.unionMemberCount(type_index);
        var wrong_size = false;
        var at: u32 = 0;
        while (at < count) : (at += 1) {
            const member = pool.unionMemberAt(type_index, at);
            assert(pool.isUnion(member) == false);
            switch (try pool.fit(gpa, value, member, widen)) {
                .value => |fitted| return .{ .value = try pool.intern(gpa, .{
                    .value_union = .{ .type = type_index, .value = fitted },
                }) },
                .does_not_fit => wrong_size = true,
                .wrong_kind => {},
            }
        }
        return if (wrong_size) .does_not_fit else .wrong_kind;
    }

    // a settled value takes its own type or a wider one
    const found = pool.typeOfValue(value);
    if (isUntyped(found) == false) {
        if (type_index == found) return .{ .value = value };
        if (widen == .allowed and widens(found, type_index)) {
            const widened: Key = switch (pool.keyOf(value)) {
                .value_int => |it| widenedInt(it.value, type_index),
                .value_float => |it| .{ .value_float = .{ .type = type_index, .value = it.value } },
                // widening answers for a number and nothing else
                else => unreachable,
            };
            return .{ .value = try pool.intern(gpa, widened) };
        }
        return switch (pool.keyOf(value)) {
            .value_union => |it| pool.fit(gpa, it.value, type_index, widen),
            else => .wrong_kind,
        };
    }

    switch (pool.keyOf(value)) {
        .value_int => |it| {
            if (isInteger(type_index)) {
                if (fitsInt(it.value, type_index) == false) return .does_not_fit;
                return .{ .value = try pool.internWith(gpa, it.value, type_index) };
            }
            if (isFloat(type_index)) {
                // an integer is exact, so a float that would round it loses a value
                const exact = exactFloat(it.value, type_index) orelse return .does_not_fit;
                return .{ .value = try pool.intern(gpa, .{
                    .value_float = .{ .type = type_index, .value = exact },
                }) };
            }
            return .wrong_kind;
        },
        .value_float => |it| {
            if (isFloat(type_index)) {
                const narrowed = narrowFloat(it.value, type_index);
                if (std.math.isInf(narrowed) and std.math.isInf(it.value) == false) {
                    return .does_not_fit;
                }
                return .{ .value = try pool.intern(gpa, .{
                    .value_float = .{ .type = type_index, .value = narrowed },
                }) };
            }
            if (isInteger(type_index)) {
                // only a whole number can stop being a float
                const truncated = @trunc(it.value);
                if (truncated != it.value) return .does_not_fit;
                if (it.value < -0x1p127 or it.value >= 0x1p127) return .does_not_fit;
                const as_int: i128 = @intFromFloat(truncated);
                if (fitsInt(as_int, type_index) == false) return .does_not_fit;
                return .{ .value = try pool.internWith(gpa, as_int, type_index) };
            }
            return .wrong_kind;
        },
        // still unchosen, so only storage or a view of it can take the elements
        .value_aggregate => switch (pool.keyOf(type_index)) {
            .type_array => |array| return pool.fitAggregate(gpa, value, array, type_index),
            .type_slice => |view| return pool.fitView(gpa, value, view, type_index),
            else => return .wrong_kind,
        },
        // only a number or an aggregate can still be untyped
        else => unreachable,
    }
}

/// The bytes the program owns, and a view of them, which is never writable.
fn fitView(
    pool: *Pool,
    gpa: Allocator,
    value: Index,
    view: Key.Slice,
    type_index: Index,
) Allocator.Error!Fit {
    if (view.mutable) return .wrong_kind;

    const array: Key.Array = .{ .child = view.child, .len = pool.aggregateLen(value) };
    const array_type = try pool.intern(gpa, .{ .type_array = array });
    const data = switch (try pool.fitAggregate(gpa, value, array, array_type)) {
        .value => |fitted| fitted,
        .does_not_fit => return .does_not_fit,
        .wrong_kind => return .wrong_kind,
    };
    return .{ .value = try pool.intern(gpa, .{
        .value_slice = .{ .type = type_index, .data = data },
    }) };
}

fn fitAggregate(
    pool: *Pool,
    gpa: Allocator,
    value: Index,
    array: Key.Array,
    type_index: Index,
) Allocator.Error!Fit {
    const count = pool.aggregateLen(value);
    if (array.len != count) return .does_not_fit;

    const mark = pool.scratch.items.len;
    defer pool.scratch.shrinkRetainingCapacity(mark);
    try pool.scratch.ensureUnusedCapacity(gpa, count);

    var at: u32 = 0;
    while (at < count) : (at += 1) {
        switch (try pool.fit(gpa, pool.aggregateAt(value, at), array.child, .refused)) {
            .value => |fitted| try pool.scratch.append(gpa, fitted),
            .does_not_fit => return .does_not_fit,
            .wrong_kind => return .wrong_kind,
        }
    }

    return .{ .value = try pool.intern(gpa, .{ .value_aggregate = .{
        .type = type_index,
        .elems = pool.scratch.items[mark..],
    } }) };
}

// the arms of the core

/// One integer and one float shape, whichever the type says.
const Number = struct {
    type: Index,
    int: i128,
    float: f64,
};

fn numberOf(key: Key) ?Number {
    return switch (key) {
        .value_int => |it| .{ .type = it.type, .int = it.value, .float = 0 },
        .value_float => |it| .{ .type = it.type, .int = 0, .float = it.value },
        else => null,
    };
}

/// The type two operands share, or null where no value of one is a value of the other.
pub fn sharedType(left: Index, right: Index) ?Index {
    if (left == right) return left;
    if (left == .untyped_int_type) return right;
    if (right == .untyped_int_type) return left;
    if (left == .untyped_float_type) return if (isFloat(right)) right else null;
    if (right == .untyped_float_type) return if (isFloat(left)) left else null;
    if (widens(left, right)) return right;
    if (widens(right, left)) return left;
    return null;
}

fn foldInt(
    pool: *Pool,
    gpa: Allocator,
    op: AST.BinaryOp,
    a: i128,
    b: i128,
    result_type: Index,
) Allocator.Error!Fold {
    assert(isInteger(result_type));
    switch (op) {
        .add, .sub, .mul => {
            const wide = switch (op) {
                .add => std.math.add(i128, a, b),
                .sub => std.math.sub(i128, a, b),
                .mul => std.math.mul(i128, a, b),
                else => unreachable,
            } catch return .overflow;
            return pool.internInt(gpa, wide, result_type);
        },
        .div => {
            if (b == 0) return .division_by_zero;
            const wide = std.math.divTrunc(i128, a, b) catch return .overflow;
            return pool.internInt(gpa, wide, result_type);
        },
        .mod => {
            if (b == 0) return .division_by_zero;
            // @rem overflows only for minInt / -1
            const wide = if (b == -1) 0 else @rem(a, b);
            return pool.internInt(gpa, wide, result_type);
        },
        .bit_and => return pool.internInt(gpa, a & b, result_type),
        .bit_or => return pool.internInt(gpa, a | b, result_type),
        .bit_xor => return pool.internInt(gpa, a ^ b, result_type),
        .shift_left => {
            const amount = shiftAmount(b, result_type) orelse {
                return .{ .bad_shift = .{ .count = b, .type = result_type } };
            };
            const wide = std.math.shlExact(i128, a, amount) catch return .overflow;
            return pool.internInt(gpa, wide, result_type);
        },
        .shift_right => {
            const amount = shiftAmount(b, result_type) orelse {
                return .{ .bad_shift = .{ .count = b, .type = result_type } };
            };
            return pool.internInt(gpa, a >> amount, result_type);
        },
        // `fold` answered every comparison, and `and` and `or` are control flow
        .equal, .not_equal, .less_than, .less_or_equal => unreachable,
        .greater_than, .greater_or_equal, .bool_and, .bool_or => unreachable,
    }
}

fn foldFloat(
    pool: *Pool,
    gpa: Allocator,
    op: AST.BinaryOp,
    a: f64,
    b: f64,
    result_type: Index,
) Allocator.Error!Fold {
    assert(isFloat(result_type));
    switch (op) {
        .add => return pool.internFloat(gpa, a + b, result_type),
        .sub => return pool.internFloat(gpa, a - b, result_type),
        .mul => return pool.internFloat(gpa, a * b, result_type),
        .div => {
            if (b == 0) return .division_by_zero;
            return pool.internFloat(gpa, a / b, result_type);
        },
        .mod, .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => {
            return .{ .bad_operand = result_type };
        },
        // `fold` answered every comparison, and `and` and `or` are control flow
        .equal, .not_equal, .less_than, .less_or_equal => unreachable,
        .greater_than, .greater_or_equal, .bool_and, .bool_or => unreachable,
    }
}

/// Where overflow in a sized type is caught.
fn internInt(
    pool: *Pool,
    gpa: Allocator,
    value: i128,
    type_index: Index,
) Allocator.Error!Fold {
    assert(isInteger(type_index));
    if (fitsInt(value, type_index) == false) {
        // interned untyped, so the report can spell the number the type would not hold
        return .{ .does_not_fit = .{
            .value = try pool.internWith(gpa, value, .untyped_int_type),
            .type = type_index,
        } };
    }
    return .{ .value = try pool.internWith(gpa, value, type_index) };
}

fn internFloat(pool: *Pool, gpa: Allocator, value: f64, type_index: Index) Allocator.Error!Fold {
    assert(isFloat(type_index));
    return .{ .value = try pool.intern(gpa, .{
        .value_float = .{ .type = type_index, .value = value },
    }) };
}

/// Into an integer type already checked to hold the value.
fn internWith(pool: *Pool, gpa: Allocator, value: i128, type_index: Index) Allocator.Error!Index {
    assert(isInteger(type_index));
    assert(fitsInt(value, type_index));
    return pool.intern(gpa, .{ .value_int = .{ .type = type_index, .value = value } });
}

/// A typed integer widened, which lands as a float where the type is one.
fn widenedInt(value: i128, into: Index) Key {
    if (isFloat(into)) {
        // `widens` admitted the type, so every value of it is exact here
        assert(exactFloat(value, into) != null);
        return .{ .value_float = .{ .type = into, .value = @floatFromInt(value) } };
    }
    return .{ .value_int = .{ .type = into, .value = value } };
}

/// Constants fold at 64 bits, so landing on an `f32` rounds to what it can hold.
fn narrowFloat(value: f64, type_index: Index) f64 {
    assert(isFloat(type_index));
    if (type_index != .f32_type) return value;
    return @floatCast(@as(f32, @floatCast(value)));
}

// storage helpers

/// Leading words, then the payload.
fn addExtra(
    pool: *Pool,
    gpa: Allocator,
    leads: []const u32,
    words: []const u32,
) Allocator.Error!u32 {
    assert(leads.len > 0);
    if (pool.extra.items.len + words.len + leads.len > std.math.maxInt(u32)) {
        return error.OutOfMemory;
    }

    // the reserve may move `extra`, so the payload must not point into it
    if (pool.extra.items.len > 0 and words.len > 0) {
        const extra_start = @intFromPtr(pool.extra.items.ptr);
        const extra_end = extra_start + pool.extra.items.len * @sizeOf(u32);
        const words_start = @intFromPtr(words.ptr);
        assert(words_start >= extra_end or words_start + words.len * @sizeOf(u32) <= extra_start);
    }

    const start: u32 = @intCast(pool.extra.items.len);
    try pool.extra.ensureUnusedCapacity(gpa, words.len + leads.len);
    pool.extra.appendSliceAssumeCapacity(leads);
    pool.extra.appendSliceAssumeCapacity(words);

    assert(pool.extra.items.len == start + words.len + leads.len);
    return start;
}

fn extraWords(pool: *const Pool, start: u32, comptime count: u32) *const [count]u32 {
    assert(start + count <= pool.extra.items.len);
    return pool.extra.items[start..][0..count];
}

fn wordsOf(value: anytype) [@divExact(@bitSizeOf(@TypeOf(value)), 32)]u32 {
    return @bitCast(value);
}

const KeyAdapter = struct {
    pool: *const Pool,

    pub fn hash(_: KeyAdapter, key: Key) u64 {
        return key.hash();
    }

    pub fn eql(adapter: KeyAdapter, key: Key, index: Index) bool {
        return key.eql(adapter.pool.keyOf(index));
    }
};

const IndexContext = struct {
    pool: *const Pool,

    pub fn hash(context: IndexContext, index: Index) u64 {
        return context.pool.keyOf(index).hash();
    }

    pub fn eql(_: IndexContext, a: Index, b: Index) bool {
        return a == b;
    }
};

const StringAdapter = struct {
    bytes: *const std.ArrayList(u8),

    pub fn hash(_: StringAdapter, text: []const u8) u64 {
        return std.hash_map.hashString(text);
    }

    pub fn eql(adapter: StringAdapter, text: []const u8, index: String) bool {
        return spells(adapter.bytes.items, index, text);
    }
};

const StringContext = struct {
    bytes: *const std.ArrayList(u8),

    pub fn hash(context: StringContext, index: String) u64 {
        return std.hash_map.hashString(std.mem.sliceTo(context.bytes.items[index.int()..], 0));
    }

    pub fn eql(_: StringContext, a: String, b: String) bool {
        return a == b;
    }
};
