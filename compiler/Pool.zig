//! One item per type and per payload.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Handle = @import("Handle.zig");
const Module = @import("Module.zig");

items: std.MultiArrayList(Item),
extra: std.ArrayList(u32),
bytes: std.ArrayList(u8),
map: std.HashMapUnmanaged(Index, void, IndexContext, load_percentage),
string_map: std.HashMapUnmanaged(String, void, StringContext, load_percentage),
/// Marked and restored. Gathers indexes a walk holds on to, which nests.
scratch: std.ArrayList(Index),
/// Small integer constants, so they skip the map. `.poison`, never a value, marks unfilled.
small_ints: [statics * small_int_range]Index,

const small_int_range = 256;

const load_percentage = std.hash_map.default_max_load_percentage;

const Pool = @This();

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
    void_type,
    untyped_int_type,
    untyped_float_type,
    untyped_aggregate_type,
    _,

    pub fn from(raw: usize) Index {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(raw);
    }

    pub fn int(index: Index) u32 {
        return @intFromEnum(index);
    }
};

pub const Instance = Handle.Index("instance");
pub const OptionalInstance = Instance.Optional;

/// An offset into `bytes`. The text runs to the next zero byte.
pub const String = enum(u32) {
    empty = 0,
    _,

    pub fn from(raw: usize) String {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(raw);
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
};

pub fn primitiveType(text: []const u8) ?Index {
    return primitives.get(text);
}

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
        if (isNumeric(simple.index()) == false or isUntyped(simple.index())) continue;
        entries[count] = .{ @tagName(simple), simple.index() };
        count += 1;
    }
    break :build std.StaticStringMap(Index).initComptime(entries[0..count].*);
};

pub const Key = union(enum) {
    type_simple: SimpleType,
    type_pointer: Pointer,
    type_array: Array,
    type_slice: Slice,
    type_struct: Instance,
    /// A nominal unit type. Never generic, so the declaration is the identity.
    type_unit: Module.Decl.Index,
    /// Ordered distinct members, none a union. Stale at the next intern.
    type_union: []const Index,

    value_int: Int,
    value_float: Float,
    /// Ordered elements. Borrowed from `extra`, stale at the next intern.
    value_aggregate: Aggregate,
    value_unit: Index,
    /// A constant that knows its union. The union, then the member constant.
    value_union: Wrapped,
    /// A view of bytes the program owns, which is what a constant becomes on a `[]T`.
    value_slice: Viewed,
    /// An array whose every element is the same, held once. The length is in the type.
    value_repeat: Repeat,

    pub const Pointer = struct { child: Index, mutable: bool };
    /// A length no layout can hold is refused where the size is asked, not here.
    pub const Array = struct { child: Index, len: u64 };
    pub const Slice = struct { child: Index, mutable: bool };
    pub const Int = struct { type: Index, value: i128 };
    pub const Float = struct { type: Index, value: f64 };
    pub const Wrapped = struct { type: Index, value: Index };
    pub const Viewed = struct { type: Index, data: Index };
    pub const Repeat = struct { type: Index, element: Index };
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
                std.hash.autoHash(&hasher, bitsOf(it.value));
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
                bitsOf(it.value) == bitsOf(other.value_float.value),
            inline else => |payload, tag| std.meta.eql(payload, @field(other, @tagName(tag))),
        };
    }
};

pub const TypeKey = union(enum) {
    type_simple: SimpleType,
    type_pointer: Key.Pointer,
    type_array: Key.Array,
    type_slice: Key.Slice,
    type_struct: Instance,
    type_unit: Module.Decl.Index,
    type_union: []const Index,
};

/// The value arms of `Key`, and `poison`, which is a broken value as much as a broken type.
pub const ValueKey = union(enum) {
    poison,
    value_int: Key.Int,
    value_float: Key.Float,
    value_aggregate: Key.Aggregate,
    value_unit: Index,
    value_union: Key.Wrapped,
    value_slice: Key.Viewed,
    value_repeat: Key.Repeat,
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
        value_repeat,
    };
};

comptime {
    assert(@sizeOf(Item.Tag) == 1);
    assert(fold_bits == @bitSizeOf(i128));
    // every integer a program can write folds without truncating
    assert(@bitSizeOf(u64) < fold_bits);
    assert(std.math.maxInt(u64) < std.math.maxInt(i128));
    assert(std.math.minInt(i64) > std.math.minInt(i128));
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

pub fn intern(pool: *Pool, gpa: Allocator, key: Key) Allocator.Error!Index {
    const small = smallIntSlot(key);
    if (small) |at| if (pool.small_ints[at] != .poison) return pool.small_ints[at];

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
            for (members, 0..) |member, at| {
                assert(pool.isType(member));
                assert(pool.isUnion(member) == false);
                for (members[0..at]) |earlier| assert(member != earlier);
            }
            break :item .{
                .tag = .type_union,
                .data = try pool.addExtra(gpa, &.{@intCast(members.len)}, @ptrCast(members)),
            };
        },
        .value_union => |it| item: {
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
        .value_repeat => |it| item: {
            assert(pool.keyOf(it.type) == .type_array);
            assert(pool.isType(it.element) == false);
            break :item .{
                .tag = .value_repeat,
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
            assert(pool.keyOf(unit_type) == .type_unit);
            break :item .{ .tag = .value_unit, .data = unit_type.int() };
        },
        .value_int => |it| .{
            .tag = .value_int,
            .data = try pool.addExtra(gpa, &.{it.type.int()}, &wordsOf(it.value)),
        },
        .value_float => |it| .{
            .tag = .value_float,
            .data = try pool.addExtra(gpa, &.{it.type.int()}, &wordsOf(bitsOf(it.value))),
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
    if (it.value < 0 or it.value >= small_int_range) return null;
    return it.type.int() * small_int_range + @as(u32, @intCast(it.value));
}

pub fn typeKey(pool: *const Pool, index: Index) TypeKey {
    assert(pool.isType(index));
    return switch (pool.keyOf(index)) {
        inline .type_simple,
        .type_pointer,
        .type_array,
        .type_slice,
        .type_struct,
        .type_unit,
        .type_union,
        => |payload, tag| @unionInit(TypeKey, @tagName(tag), payload),
        else => unreachable,
    };
}

pub fn valueKey(pool: *const Pool, index: Index) ValueKey {
    if (index == .poison) return .poison;
    assert(pool.isType(index) == false);
    return switch (pool.keyOf(index)) {
        inline .value_int,
        .value_float,
        .value_aggregate,
        .value_unit,
        .value_union,
        .value_slice,
        .value_repeat,
        => |payload, tag| @unionInit(ValueKey, @tagName(tag), payload),
        else => unreachable,
    };
}

pub fn keyOf(pool: *const Pool, index: Index) Key {
    assert(index.int() < pool.items.len);

    const data = pool.items.items(.data)[index.int()];
    const extra = pool.extra.items;
    return switch (pool.items.items(.tag)[index.int()]) {
        .type_simple => .{ .type_simple = @enumFromInt(data) },
        .type_pointer => .{ .type_pointer = .{ .child = @enumFromInt(data), .mutable = false } },
        .type_pointer_var => .{ .type_pointer = .{ .child = @enumFromInt(data), .mutable = true } },
        .type_array => .{ .type_array = .{
            .child = @enumFromInt(extra[data]),
            .len = @bitCast(pool.extraWords(data + 1, 2).*),
        } },
        .type_slice => .{ .type_slice = .{ .child = @enumFromInt(data), .mutable = false } },
        .type_slice_var => .{ .type_slice = .{ .child = @enumFromInt(data), .mutable = true } },
        .type_struct => .{ .type_struct = @enumFromInt(data) },
        .type_unit => .{ .type_unit = @enumFromInt(data) },
        .type_union => .{ .type_union = pool.unionMembers(index) },
        .value_aggregate => .{ .value_aggregate = .{
            .type = @enumFromInt(extra[data]),
            .elems = @ptrCast(extra[data + 2 ..][0..extra[data + 1]]),
        } },
        .value_unit => .{ .value_unit = @enumFromInt(data) },
        .value_union => .{ .value_union = .{
            .type = @enumFromInt(extra[data]),
            .value = @enumFromInt(extra[data + 1]),
        } },
        .value_slice => .{ .value_slice = .{
            .type = @enumFromInt(extra[data]),
            .data = @enumFromInt(extra[data + 1]),
        } },
        .value_repeat => .{ .value_repeat = .{
            .type = @enumFromInt(extra[data]),
            .element = @enumFromInt(extra[data + 1]),
        } },
        .value_int => .{ .value_int = .{
            .type = @enumFromInt(extra[data]),
            .value = @bitCast(pool.extraWords(data + 1, 4).*),
        } },
        .value_float => .{ .value_float = .{
            .type = @enumFromInt(extra[data]),
            .value = @bitCast(@as(u64, @bitCast(pool.extraWords(data + 1, 2).*))),
        } },
    };
}

pub const union_members_max = 255;

pub const Unite = union(enum) {
    index: Index,
    /// Already in the flattened list. An alias is not a new type.
    duplicate: Index,
    too_wide,
};

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
    if (pool.isUnion(member)) return false;
    return std.mem.indexOfScalar(Index, pool.unionMembers(union_index), member) != null;
}

pub fn memberPosition(pool: *const Pool, union_index: Index, member: Index) u32 {
    const at = std.mem.indexOfScalar(Index, pool.unionMembers(union_index), member);
    return @intCast(at orelse unreachable); // callers ask only about a member
}

/// `part` is `set` itself or one member of it. A union is never a member.
pub fn covers(pool: *const Pool, set: Index, part: Index) bool {
    if (set == part) return true;
    return pool.isUnion(set) and pool.unionHas(set, part);
}

/// Every alternative of `narrow` is one of `wide`.
pub fn subsumes(pool: *const Pool, wide: Index, narrow: Index) bool {
    if (pool.isUnion(narrow) == false) return pool.covers(wide, narrow);
    for (pool.unionMembers(narrow)) |member| if (pool.covers(wide, member) == false) return false;
    return true;
}

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

pub fn unionTail(pool: *Pool, gpa: Allocator, union_index: Index) Allocator.Error!Index {
    const rest = try pool.unionWithout(gpa, union_index, pool.unionMemberAt(union_index, 0));
    return rest orelse unreachable; // a union holds two members or more
}

/// Borrowed from `extra`, stale at the next intern. A walk that interns uses `membersOf`.
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

/// The members by position, each read fresh, so the walk may intern between them.
pub const Members = struct {
    pool: *const Pool,
    index: Index,
    at: u32 = 0,

    pub fn next(it: *Members) ?Index {
        if (it.at == it.pool.unionMemberCount(it.index)) return null;
        defer it.at += 1;
        return it.pool.unionMemberAt(it.index, it.at);
    }
};

pub fn membersOf(pool: *const Pool, index: Index) Members {
    assert(pool.isUnion(index));
    return .{ .pool = pool, .index = index };
}

/// A union's first member, and any other type itself.
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
    for (text, 0..) |byte, at| if (stored[at] != byte) return false;
    return stored[text.len] == 0;
}

pub fn stringText(pool: *const Pool, index: String) []const u8 {
    assert(index.int() < pool.bytes.items.len);
    return std.mem.sliceTo(pool.bytes.items[index.int()..], 0);
}

pub fn typeOfValue(pool: *const Pool, value: Index) Index {
    return switch (pool.valueKey(value)) {
        .poison => .poison,
        .value_unit => |unit_type| unit_type,
        inline else => |it| it.type,
    };
}

pub fn memberOfValue(pool: *const Pool, value: Index) Index {
    return switch (pool.keyOf(value)) {
        .value_union => |it| pool.typeOfValue(it.value),
        else => pool.typeOfValue(value),
    };
}

pub fn heldValue(pool: *const Pool, value: Index) Index {
    return pool.keyOf(value).value_union.value;
}

/// Whether a union constant holds its type's first member, the edge a condition takes.
pub fn holdsFirst(pool: *const Pool, value: Index) bool {
    return pool.memberOfValue(value) == pool.firstMember(pool.typeOfValue(value));
}

pub fn int(pool: *Pool, gpa: Allocator, type_index: Index, value: i128) Allocator.Error!Index {
    assert(isInteger(type_index));
    assert(fitsInt(value, type_index));
    return pool.intern(gpa, .{ .value_int = .{ .type = type_index, .value = value } });
}

/// An integer constant retyped to `wanted`, or null where the type does not hold it.
pub fn castInt(pool: *Pool, gpa: Allocator, value: Index, wanted: Index) Allocator.Error!?Index {
    assert(isSizedInt(wanted));
    const written = pool.keyOf(value).value_int.value;
    if (fitsInt(written, wanted) == false) return null;
    return try pool.int(gpa, wanted, written);
}

pub fn unitValue(pool: *Pool, gpa: Allocator, unit_type: Index) Allocator.Error!Index {
    return pool.intern(gpa, .{ .value_unit = unit_type });
}

/// `value` as a constant of `union_type`. One already in a union enters as what it holds.
pub fn enter(pool: *Pool, gpa: Allocator, union_type: Index, value: Index) Allocator.Error!Index {
    const held = switch (pool.keyOf(value)) {
        .value_union => |it| it.value,
        else => value,
    };
    return pool.intern(gpa, .{ .value_union = .{ .type = union_type, .value = held } });
}

/// A union constant narrowed to `wanted`, which is poison where it holds no member of it.
pub fn narrowTo(pool: *Pool, gpa: Allocator, value: Index, wanted: Index) Allocator.Error!Index {
    if (value == .poison) return .poison;
    const held = pool.heldValue(value);
    if (pool.covers(wanted, pool.typeOfValue(held)) == false) return .poison;
    if (pool.isUnion(wanted) == false) return held;
    return pool.enter(gpa, wanted, held);
}

/// Yes or no in `bools`, two unit members of which the first means yes.
pub fn truth(pool: *Pool, gpa: Allocator, bools: Index, holds: bool) Allocator.Error!Index {
    if (bools == .poison) return .poison;
    const member = pool.unionMemberAt(bools, if (holds) 0 else 1);
    return pool.enter(gpa, bools, try pool.unitValue(gpa, member));
}

pub fn structOf(pool: *const Pool, index: Index) Instance {
    return pool.keyOf(index).type_struct;
}

pub fn isType(pool: *const Pool, index: Index) bool {
    assert(index.int() < pool.items.len);
    return switch (pool.items.items(.tag)[index.int()]) {
        .type_simple, .type_pointer, .type_pointer_var, .type_array => true,
        .type_slice, .type_slice_var, .type_struct, .type_unit, .type_union => true,
        .value_int, .value_float, .value_aggregate => false,
        .value_unit, .value_union, .value_slice, .value_repeat => false,
    };
}

/// With `aggregateAt`, for walks that intern. `keyOf` only borrows.
pub fn aggregateLen(pool: *const Pool, index: Index) u64 {
    return switch (pool.keyOf(index)) {
        .value_aggregate => |it| it.elems.len,
        .value_repeat => |it| pool.keyOf(it.type).type_array.len,
        else => unreachable,
    };
}

pub fn aggregateAt(pool: *const Pool, index: Index, at: u64) Index {
    assert(at < pool.aggregateLen(index));
    return switch (pool.keyOf(index)) {
        .value_aggregate => |it| it.elems[@intCast(at)],
        .value_repeat => |it| it.element,
        else => unreachable,
    };
}

pub fn isInteger(index: Index) bool {
    return isSizedInt(index) or index == .untyped_int_type;
}

pub fn isSizedInt(index: Index) bool {
    return switch (index) {
        .i8_type, .i16_type, .i32_type, .i64_type => true,
        .u8_type, .u16_type, .u32_type, .u64_type => true,
        else => false,
    };
}

pub fn isSignedInt(index: Index) bool {
    return switch (index) {
        .i8_type, .i16_type, .i32_type, .i64_type => true,
        else => false,
    };
}

pub fn isFloat(index: Index) bool {
    return isSizedFloat(index) or index == .untyped_float_type;
}

pub fn isSizedFloat(index: Index) bool {
    return index == .f32_type or index == .f64_type;
}

pub fn isNumeric(index: Index) bool {
    return isInteger(index) or isFloat(index);
}

pub fn isSignedNumber(index: Index) bool {
    return isSignedInt(index) or isSizedFloat(index);
}

pub fn isUntyped(index: Index) bool {
    return switch (index) {
        .untyped_int_type, .untyped_float_type, .untyped_aggregate_type => true,
        else => false,
    };
}

pub fn widens(from: Index, into: Index) bool {
    if (from == .f32_type) return into == .f64_type;
    if (isSizedInt(from) == false) return false;
    if (isSizedFloat(into)) {
        return minInt(from) >= -exactIntMax(into) and maxInt(from) <= exactIntMax(into);
    }
    if (isSizedInt(into) == false) return false;
    return minInt(into) <= minInt(from) and maxInt(from) <= maxInt(into);
}

fn exactIntMax(float_type: Index) i128 {
    return switch (float_type) {
        .f32_type => 1 << 24,
        .f64_type => 1 << 53,
        else => unreachable,
    };
}

fn exactFloat(value: i128, type_index: Index) ?f64 {
    assert(isFloat(type_index));
    const wide = narrowFloat(@floatFromInt(value), type_index);
    if (wide < -0x1p127 or wide >= 0x1p127) return null;
    if (@as(i128, @intFromFloat(wide)) != value) return null;
    return wide;
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

pub fn fitsInt(value: i128, type_index: Index) bool {
    assert(isNumeric(type_index));
    if (isSizedInt(type_index) == false) return true;
    return minInt(type_index) <= value and value <= maxInt(type_index);
}

pub fn widthOf(type_index: Index) u16 {
    return switch (type_index) {
        .i8_type, .u8_type => 8,
        .i16_type, .u16_type => 16,
        .i32_type, .u32_type => 32,
        .i64_type, .u64_type => 64,
        .untyped_int_type => fold_bits,
        else => unreachable,
    };
}

pub const Fold = union(enum) {
    value: Index,
    overflow,
    division_by_zero,
    bad_shift: struct { count: i128, type: Index },
    does_not_fit: struct { value: Index, type: Index },
    mismatch: struct { left: Index, right: Index },
    bad_operand: Index,
    /// A comparison's answer, spelled by the checker, because `bool` is declared.
    truth: bool,
};

pub const fold_bits = 128;

pub fn fold(
    pool: *Pool,
    gpa: Allocator,
    op: AST.BinaryOp,
    lhs: Index,
    rhs: Index,
) Allocator.Error!Fold {
    if (lhs == .poison or rhs == .poison) return .{ .value = .poison };
    assert(op != .bool_and);
    assert(op != .bool_or);

    const left = numberOf(pool.keyOf(lhs)) orelse return .{ .bad_operand = pool.typeOfValue(lhs) };
    const right = numberOf(pool.keyOf(rhs)) orelse return .{ .bad_operand = pool.typeOfValue(rhs) };
    const result_type = sharedType(left.type, right.type) orelse {
        return .{ .mismatch = .{ .left = left.type, .right = right.type } };
    };

    // through fit, so a constant that would round is refused as at run time
    const a = try pool.fitNumber(gpa, lhs, result_type) orelse {
        return .{ .does_not_fit = .{ .value = lhs, .type = result_type } };
    };
    const b = try pool.fitNumber(gpa, rhs, result_type) orelse {
        return .{ .does_not_fit = .{ .value = rhs, .type = result_type } };
    };

    if (isFloat(result_type)) {
        if (compared(op, a.float, b.float)) |holds| return .{ .truth = holds };
        const value: f64 = switch (op) {
            .add => a.float + b.float,
            .sub => a.float - b.float,
            .mul => a.float * b.float,
            .div => if (b.float == 0) return .division_by_zero else a.float / b.float,
            else => return .{ .bad_operand = result_type },
        };
        return pool.internFloat(gpa, value, result_type);
    }

    if (compared(op, a.int, b.int)) |holds| return .{ .truth = holds };
    const value: i128 = switch (op) {
        .add => std.math.add(i128, a.int, b.int) catch return .overflow,
        .sub => std.math.sub(i128, a.int, b.int) catch return .overflow,
        .mul => std.math.mul(i128, a.int, b.int) catch return .overflow,
        .div => if (b.int == 0)
            return .division_by_zero
        else
            std.math.divTrunc(i128, a.int, b.int) catch return .overflow,
        .mod => if (b.int == 0)
            return .division_by_zero
        else if (b.int == -1)
            0
        else
            @rem(a.int, b.int),
        .bit_and => a.int & b.int,
        .bit_or => a.int | b.int,
        .bit_xor => a.int ^ b.int,
        .shift_left, .shift_right => shifted: {
            if (b.int < 0 or b.int >= widthOf(result_type)) {
                return .{ .bad_shift = .{ .count = b.int, .type = result_type } };
            }
            const amount: std.math.Log2Int(i128) = @intCast(b.int);
            if (op == .shift_right) break :shifted a.int >> amount;
            break :shifted std.math.shlExact(i128, a.int, amount) catch return .overflow;
        },
        // comparisons returned above, `and` and `or` never fold
        else => unreachable,
    };
    return pool.internInt(gpa, value, result_type);
}

fn compared(op: AST.BinaryOp, a: anytype, b: @TypeOf(a)) ?bool {
    return switch (op) {
        .equal => a == b,
        .not_equal => a != b,
        .less_than => a < b,
        .less_or_equal => a <= b,
        .greater_than => a > b,
        .greater_or_equal => a >= b,
        else => null,
    };
}

fn fitNumber(pool: *Pool, gpa: Allocator, value: Index, type_index: Index) Allocator.Error!?Number {
    return switch (try pool.fit(gpa, value, type_index, .allowed)) {
        .value => |fitted| numberOf(pool.keyOf(fitted)),
        .does_not_fit, .wrong_kind => null,
    };
}

pub fn foldNegate(pool: *Pool, gpa: Allocator, operand: Index) Allocator.Error!Fold {
    if (operand == .poison) return .{ .value = .poison };
    const number = numberOf(pool.keyOf(operand)) orelse {
        return .{ .bad_operand = pool.typeOfValue(operand) };
    };
    if (isFloat(number.type)) return pool.internFloat(gpa, -number.float, number.type);
    const negated = std.math.negate(number.int) catch return .overflow;
    return pool.internInt(gpa, negated, number.type);
}

pub fn foldBitNot(pool: *Pool, gpa: Allocator, operand: Index) Allocator.Error!Fold {
    if (operand == .poison) return .{ .value = .poison };
    const number = numberOf(pool.keyOf(operand)) orelse {
        return .{ .bad_operand = pool.typeOfValue(operand) };
    };
    if (isInteger(number.type) == false) return .{ .bad_operand = number.type };
    assert(fitsInt(number.int, number.type));

    var complement = ~number.int;
    if (isSizedInt(number.type) and isSignedInt(number.type) == false) {
        complement &= (@as(i128, 1) << @intCast(widthOf(number.type))) - 1;
    }
    return pool.internInt(gpa, complement, number.type);
}

pub const Fit = union(enum) {
    value: Index,
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
    if (value == .poison or type_index == .poison) return .{ .value = .poison };
    assert(pool.isType(type_index));

    // the first fitting member decides
    if (pool.isUnion(type_index)) {
        var wrong_size = false;
        var members = pool.membersOf(type_index);
        while (members.next()) |member| {
            switch (try pool.fit(gpa, value, member, widen)) {
                .value => |fitted| return .{ .value = try pool.enter(gpa, type_index, fitted) },
                .does_not_fit => wrong_size = true,
                .wrong_kind => {},
            }
        }
        return if (wrong_size) .does_not_fit else .wrong_kind;
    }

    const found = pool.typeOfValue(value);
    if (isUntyped(found) == false) {
        if (type_index == found) return .{ .value = value };
        if (widen == .allowed and widens(found, type_index)) {
            switch (pool.keyOf(value)) {
                .value_int => |it| return .{
                    .value = try pool.internNumber(gpa, it.value, type_index),
                },
                .value_float => |it| return .{ .value = try pool.intern(gpa, .{
                    .value_float = .{ .type = type_index, .value = it.value },
                }) },
                else => {},
            }
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
                return .{ .value = try pool.int(gpa, type_index, it.value) };
            }
            if (isFloat(type_index)) {
                // an integer is exact, so a float that would round it loses a value
                if (exactFloat(it.value, type_index) == null) return .does_not_fit;
                return .{ .value = try pool.internNumber(gpa, it.value, type_index) };
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
                if (@trunc(it.value) != it.value) return .does_not_fit;
                if (it.value < -0x1p127 or it.value >= 0x1p127) return .does_not_fit;
                const as_int: i128 = @intFromFloat(it.value);
                if (fitsInt(as_int, type_index) == false) return .does_not_fit;
                return .{ .value = try pool.int(gpa, type_index, as_int) };
            }
            return .wrong_kind;
        },
        .value_aggregate => switch (pool.keyOf(type_index)) {
            .type_array => |array| return pool.fitAggregate(gpa, value, array, type_index),
            .type_slice => |view| return pool.fitView(gpa, value, view, type_index),
            else => return .wrong_kind,
        },
        else => return .wrong_kind,
    }
}

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

fn internInt(pool: *Pool, gpa: Allocator, value: i128, type_index: Index) Allocator.Error!Fold {
    assert(isInteger(type_index));
    if (fitsInt(value, type_index)) return .{ .value = try pool.int(gpa, type_index, value) };
    return .{ .does_not_fit = .{
        .value = try pool.int(gpa, .untyped_int_type, value),
        .type = type_index,
    } };
}

fn internFloat(pool: *Pool, gpa: Allocator, value: f64, type_index: Index) Allocator.Error!Fold {
    assert(isFloat(type_index));
    return .{ .value = try pool.intern(gpa, .{
        .value_float = .{ .type = type_index, .value = value },
    }) };
}

fn internNumber(pool: *Pool, gpa: Allocator, value: i128, type_index: Index) Allocator.Error!Index {
    if (isInteger(type_index)) return pool.int(gpa, type_index, value);
    const exact = exactFloat(value, type_index) orelse unreachable; // callers checked the fit
    return pool.intern(gpa, .{ .value_float = .{ .type = type_index, .value = exact } });
}

/// Constants fold at 64 bits, so landing on an `f32` rounds to what it can hold.
fn narrowFloat(value: f64, type_index: Index) f64 {
    assert(isFloat(type_index));
    if (type_index != .f32_type) return value;
    return @floatCast(@as(f32, @floatCast(value)));
}

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

fn bitsOf(value: f64) u64 {
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
