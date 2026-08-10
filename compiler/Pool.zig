//! One item per type and per constant, so equality is index equality.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Module = @import("Module.zig");

items: std.MultiArrayList(Item),
/// Wide payloads, each a type and its value words.
extra: std.ArrayList(u32),
/// Every interned string, null terminated.
bytes: std.ArrayList(u8),
/// Item lookup, so one (tag, payload) is one index forever.
map: std.HashMapUnmanaged(Index, void, IndexContext, load_percentage),
string_map: std.HashMapUnmanaged(String, void, StringContext, load_percentage),
/// Marked and restored. Gathers an aggregate's elements, which nests.
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
pub const Instance = enum(u32) {
    _,

    pub fn from(raw: usize) Instance {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(@as(u32, @intCast(raw)));
    }

    pub fn int(index: Instance) u32 {
        return @intFromEnum(index);
    }

    pub fn toOptional(index: Instance) OptionalInstance {
        const optional: OptionalInstance = @enumFromInt(@intFromEnum(index));
        assert(optional != .none);
        return optional;
    }
};

pub const OptionalInstance = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn unwrap(optional: OptionalInstance) ?Instance {
        if (optional == .none) return null;
        return @enumFromInt(@intFromEnum(optional));
    }
};

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
    /// The one value of a unit type.
    value_unit: Index,
    /// A constant that knows its union. The union, then the member constant.
    value_union: Wrapped,

    pub const Pointer = struct { child: Index, mutable: bool };
    /// A length no layout can hold is refused where the size is asked, not here.
    pub const Array = struct { child: Index, len: u64 };
    pub const Slice = struct { child: Index, mutable: bool };
    pub const Int = struct { type: Index, value: i128 };
    pub const Float = struct { type: Index, value: f64 };
    pub const Wrapped = struct { type: Index, value: Index };
    pub const Aggregate = struct { type: Index, elems: []const Index };

    fn hash(key: Key) u64 {
        const seed: u64 = @intFromEnum(std.meta.activeTag(key));
        switch (key) {
            .type_simple => |simple| return hashWords(seed, .{@intFromEnum(simple)}),
            .type_pointer => |pointer| return hashWords(seed, .{
                pointer.child.int(),
                @intFromBool(pointer.mutable),
            }),
            .type_array => |array| {
                const len: [2]u32 = @bitCast(array.len);
                return hashWords(seed, .{ array.child.int(), len[0], len[1] });
            },
            .type_slice => |slice| return hashWords(seed, .{
                slice.child.int(),
                @intFromBool(slice.mutable),
            }),
            .type_struct => |instance| return hashWords(seed, .{instance.int()}),
            .type_unit => |decl| return hashWords(seed, .{decl.int()}),
            .type_union => |members| {
                return std.hash.Wyhash.hash(seed, std.mem.sliceAsBytes(members));
            },
            .value_aggregate => |it| {
                var hasher: std.hash.Wyhash = .init(seed);
                hasher.update(std.mem.asBytes(&it.type));
                hasher.update(std.mem.sliceAsBytes(it.elems));
                return hasher.final();
            },
            .value_unit => |unit_type| return hashWords(seed, .{unit_type.int()}),
            .value_union => |it| return hashWords(seed, .{ it.type.int(), it.value.int() }),
            .value_int => |it| {
                const value: [4]u32 = @bitCast(it.value);
                return hashWords(seed, .{ it.type.int(), value[0], value[1], value[2], value[3] });
            },
            .value_float => |it| {
                const bits: [2]u32 = @bitCast(it.value);
                return hashWords(seed, .{ it.type.int(), bits[0], bits[1] });
            },
        }
    }

    fn hashWords(seed: u64, words: anytype) u64 {
        const array: [words.len]u32 = words;
        return std.hash.Wyhash.hash(seed, std.mem.asBytes(&array));
    }

    fn eql(key: Key, other: Key) bool {
        if (std.meta.activeTag(key) != std.meta.activeTag(other)) return false;
        return switch (key) {
            .type_simple => |simple| simple == other.type_simple,
            .type_pointer => |pointer| pointer.child == other.type_pointer.child and
                pointer.mutable == other.type_pointer.mutable,
            .type_array => |array| array.child == other.type_array.child and
                array.len == other.type_array.len,
            .type_slice => |slice| slice.child == other.type_slice.child and
                slice.mutable == other.type_slice.mutable,
            .type_struct => |instance| instance == other.type_struct,
            .type_unit => |decl| decl == other.type_unit,
            .type_union => |members| std.mem.eql(Index, members, other.type_union),
            .value_aggregate => |it| it.type == other.value_aggregate.type and
                std.mem.eql(Index, it.elems, other.value_aggregate.elems),
            .value_unit => |unit_type| unit_type == other.value_unit,
            .value_union => |it| it.type == other.value_union.type and
                it.value == other.value_union.value,
            .value_int => |it| it.type == other.value_int.type and
                it.value == other.value_int.value,
            // by bits, so float equality is never asked
            .value_float => |it| it.type == other.value_float.type and
                @as(u64, @bitCast(it.value)) == @as(u64, @bitCast(other.value_float.value)),
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
        .type_union => .{
            .type_union = @ptrCast(pool.extra.items[data + 1 ..][0..pool.extra.items[data]]),
        },
        .value_aggregate => .{ .value_aggregate = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .elems = @ptrCast(pool.extra.items[data + 2 ..][0..pool.extra.items[data + 1]]),
        } },
        .value_unit => .{ .value_unit = @enumFromInt(data) },
        .value_union => .{ .value_union = .{
            .type = @enumFromInt(pool.extra.items[data]),
            .value = @enumFromInt(pool.extra.items[data + 1]),
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
    assert(pool.isUnion(union_index));
    if (pool.isUnion(member)) return null;

    const count = pool.unionMemberCount(union_index);
    var at: u32 = 0;
    while (at < count) : (at += 1) {
        if (pool.unionMemberAt(union_index, at) == member) return at;
    }
    return null;
}

/// The union without one member. The rest as a union, or the one member left.
pub fn unionWithout(
    pool: *Pool,
    gpa: Allocator,
    union_index: Index,
    member: Index,
) Allocator.Error!Index {
    assert(pool.isUnion(union_index));
    assert(pool.unionHas(union_index, member));

    var flat: [union_members_max]Index = undefined;
    var count: u32 = 0;
    const total = pool.unionMemberCount(union_index);
    var at: u32 = 0;
    while (at < total) : (at += 1) {
        const candidate = pool.unionMemberAt(union_index, at);
        if (candidate == member) continue;
        flat[count] = candidate;
        count += 1;
    }
    assert(count == total - 1);

    if (count == 1) return flat[0];
    return pool.intern(gpa, .{ .type_union = flat[0..count] });
}

/// Whether `wide` lists every member of `narrow`. Membership, not order.
pub fn unionCovers(pool: *const Pool, wide: Index, narrow: Index) bool {
    assert(pool.isUnion(wide));
    assert(pool.isUnion(narrow));

    const count = pool.unionMemberCount(narrow);
    var at: u32 = 0;
    while (at < count) : (at += 1) {
        if (pool.unionHas(wide, pool.unionMemberAt(narrow, at)) == false) return false;
    }
    return true;
}

/// With `unionMemberAt`, for walks that intern. `keyOf` only borrows.
pub fn unionMemberCount(pool: *const Pool, index: Index) u32 {
    assert(pool.isUnion(index));
    return pool.extra.items[pool.items.items(.data)[index.int()]];
}

pub fn unionMemberAt(pool: *const Pool, index: Index, at: u32) Index {
    assert(at < pool.unionMemberCount(index));
    const data = pool.items.items(.data)[index.int()];
    return @enumFromInt(pool.extra.items[data + 1 + at]);
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
        .value_unit, .value_union => false,
    };
}

/// With `aggregateAt`, for walks that intern. `keyOf` only borrows.
pub fn aggregateLen(pool: *const Pool, index: Index) u32 {
    assert(pool.items.items(.tag)[index.int()] == .value_aggregate);
    return pool.extra.items[pool.items.items(.data)[index.int()] + 1];
}

pub fn aggregateAt(pool: *const Pool, index: Index, at: u32) Index {
    assert(at < pool.aggregateLen(index));
    const data = pool.items.items(.data)[index.int()];
    return @enumFromInt(pool.extra.items[data + 2 + at]);
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

pub fn fitsInt(value: i128, type_index: Index) bool {
    assert(isInteger(type_index) or isFloat(type_index));
    return switch (type_index) {
        .i8_type => value >= std.math.minInt(i8) and value <= std.math.maxInt(i8),
        .i16_type => value >= std.math.minInt(i16) and value <= std.math.maxInt(i16),
        .i32_type => value >= std.math.minInt(i32) and value <= std.math.maxInt(i32),
        .i64_type => value >= std.math.minInt(i64) and value <= std.math.maxInt(i64),
        .u8_type => value >= 0 and value <= std.math.maxInt(u8),
        .u16_type => value >= 0 and value <= std.math.maxInt(u16),
        .u32_type => value >= 0 and value <= std.math.maxInt(u32),
        .u64_type => value >= 0 and value <= std.math.maxInt(u64),
        .untyped_int_type => true,
        // every i128 is below the smallest float infinity
        .f32_type, .f64_type, .untyped_float_type => true,
        else => unreachable,
    };
}

// the constant-folding core

/// Everything except `value` is a mistake, reported at the operator.
pub const Fold = union(enum) {
    value: Index,
    /// Past the 128 bits constants fold in.
    overflow,
    division_by_zero,
    /// Outside `0 ..< 128`, the width constants fold in.
    bad_shift: i128,
    /// Refused by the type both operands carry.
    does_not_fit: struct { value: i128, type: Index },
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

    const left = pool.keyOf(lhs);
    const right = pool.keyOf(rhs);

    assert(op != .bool_and);
    assert(op != .bool_or);

    const a = numberOf(left) orelse return .{ .bad_operand = pool.typeOfValue(lhs) };
    const b = numberOf(right) orelse return .{ .bad_operand = pool.typeOfValue(rhs) };

    const result_type = sharedType(a.type, b.type) orelse {
        return .{ .mismatch = .{ .left = a.type, .right = b.type } };
    };

    if (isFloat(result_type)) {
        return pool.foldFloat(gpa, op, a.toFloat(), b.toFloat(), result_type);
    }
    return pool.foldInt(gpa, op, a.int, b.int, result_type);
}

pub fn foldNegate(pool: *Pool, gpa: Allocator, operand: Index) Allocator.Error!Fold {
    if (operand == .poison) return .{ .value = .poison };

    const number = numberOf(pool.keyOf(operand)) orelse {
        return .{ .bad_operand = pool.typeOfValue(operand) };
    };
    if (isFloat(number.type)) {
        return pool.internFloat(gpa, -number.toFloat(), number.type);
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

/// Unsigned complements inside the width, everything else in two's complement.
fn complementOf(value: i128, type_index: Index) i128 {
    assert(isInteger(type_index));
    assert(fitsInt(value, type_index));

    return switch (type_index) {
        .u8_type => ~value & 0xff,
        .u16_type => ~value & 0xffff,
        .u32_type => ~value & 0xffff_ffff,
        .u64_type => ~value & 0xffff_ffff_ffff_ffff,
        else => ~value,
    };
}

/// Null outside `0 ..< fold_bits`, which bounds every type Phi has.
fn shiftAmount(count: i128) ?std.math.Log2Int(i128) {
    if (count < 0) return null;
    if (count >= fold_bits) return null;
    return @intCast(count);
}

pub const Fit = union(enum) {
    value: Index,
    /// Right in kind, wrong in size.
    does_not_fit,
    wrong_kind,
};

/// An untyped constant meets any type its value fits, a typed one only its own.
pub fn fit(pool: *Pool, gpa: Allocator, value: Index, type_index: Index) Allocator.Error!Fit {
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
            switch (try pool.fit(gpa, value, member)) {
                .value => |fitted| return .{ .value = try pool.intern(gpa, .{
                    .value_union = .{ .type = type_index, .value = fitted },
                }) },
                .does_not_fit => wrong_size = true,
                .wrong_kind => {},
            }
        }
        return if (wrong_size) .does_not_fit else .wrong_kind;
    }

    switch (pool.keyOf(value)) {
        .value_union => |it| {
            if (type_index == it.type) return .{ .value = value };
            return pool.fit(gpa, it.value, type_index);
        },
        .value_int => |it| {
            if (isUntyped(it.type) == false) {
                return if (type_index == it.type) .{ .value = value } else .wrong_kind;
            }
            if (isInteger(type_index)) {
                if (fitsInt(it.value, type_index) == false) return .does_not_fit;
                return .{ .value = try pool.internWith(gpa, it.value, type_index) };
            }
            if (isFloat(type_index)) {
                return .{ .value = try pool.internWith(gpa, it.value, type_index) };
            }
            return .wrong_kind;
        },
        .value_float => |it| {
            if (isUntyped(it.type) == false) {
                return if (type_index == it.type) .{ .value = value } else .wrong_kind;
            }
            if (isFloat(type_index)) {
                const wide = it.value;
                const narrowed: f64 = if (type_index == .f32_type)
                    @floatCast(@as(f32, @floatCast(wide)))
                else
                    wide;
                if (std.math.isInf(narrowed) and std.math.isInf(wide) == false) {
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
        .value_aggregate => |it| {
            if (isUntyped(it.type) == false) {
                return if (type_index == it.type) .{ .value = value } else .wrong_kind;
            }
            const array = switch (pool.keyOf(type_index)) {
                .type_array => |found| found,
                else => return .wrong_kind,
            };
            return pool.fitAggregate(gpa, value, array, type_index);
        },
        .value_unit => |unit_type| {
            return if (type_index == unit_type) .{ .value = value } else .wrong_kind;
        },
        .type_simple, .type_pointer, .type_array, .type_slice => unreachable,
        .type_struct, .type_unit, .type_union => unreachable,
    }
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
        switch (try pool.fit(gpa, pool.aggregateAt(value, at), array.child)) {
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

/// Widened, so the fold has one integer and one float shape.
const Number = struct {
    type: Index,
    int: i128,
    float: f64,

    fn toFloat(number: Number) f64 {
        if (isFloat(number.type)) return number.float;
        return @floatFromInt(number.int);
    }
};

fn numberOf(key: Key) ?Number {
    return switch (key) {
        .value_int => |it| .{ .type = it.type, .int = it.value, .float = 0 },
        .value_float => |it| .{ .type = it.type, .int = 0, .float = it.value },
        else => null,
    };
}

/// The type two operands share, or null. An untyped operand takes the other.
fn sharedType(left: Index, right: Index) ?Index {
    if (left == right) return left;
    if (left == .untyped_int_type) return right;
    if (right == .untyped_int_type) return left;
    if (left == .untyped_float_type) return if (isFloat(right)) right else null;
    if (right == .untyped_float_type) return if (isFloat(left)) left else null;
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
            const amount = shiftAmount(b) orelse return .{ .bad_shift = b };
            const wide = std.math.shlExact(i128, a, amount) catch return .overflow;
            return pool.internInt(gpa, wide, result_type);
        },
        .shift_right => {
            const amount = shiftAmount(b) orelse return .{ .bad_shift = b };
            return pool.internInt(gpa, a >> amount, result_type);
        },
        .equal => return boolFold(a == b),
        .not_equal => return boolFold(a != b),
        .less_than => return boolFold(a < b),
        .less_or_equal => return boolFold(a <= b),
        .greater_than => return boolFold(a > b),
        .greater_or_equal => return boolFold(a >= b),
        .bool_and, .bool_or => unreachable,
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
        .equal => return boolFold(a == b),
        .not_equal => return boolFold(a != b),
        .less_than => return boolFold(a < b),
        .less_or_equal => return boolFold(a <= b),
        .greater_than => return boolFold(a > b),
        .greater_or_equal => return boolFold(a >= b),
        .bool_and, .bool_or => unreachable,
    }
}

fn boolFold(value: bool) Fold {
    return .{ .truth = value };
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
        return .{ .does_not_fit = .{ .value = value, .type = type_index } };
    }
    return .{ .value = try pool.intern(gpa, .{
        .value_int = .{ .type = type_index, .value = value },
    }) };
}

fn internFloat(pool: *Pool, gpa: Allocator, value: f64, type_index: Index) Allocator.Error!Fold {
    assert(isFloat(type_index));
    return .{ .value = try pool.intern(gpa, .{
        .value_float = .{ .type = type_index, .value = value },
    }) };
}

/// Into a type already checked to hold the value.
fn internWith(pool: *Pool, gpa: Allocator, value: i128, type_index: Index) Allocator.Error!Index {
    if (isFloat(type_index)) {
        const wide: f64 = @floatFromInt(value);
        const narrowed: f64 = if (type_index == .f32_type)
            @floatCast(@as(f32, @floatCast(wide)))
        else
            wide;
        return pool.intern(gpa, .{ .value_float = .{ .type = type_index, .value = narrowed } });
    }
    assert(fitsInt(value, type_index));
    return pool.intern(gpa, .{ .value_int = .{ .type = type_index, .value = value } });
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
