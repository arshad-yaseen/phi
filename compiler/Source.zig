const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");

path: []const u8,
/// The file, with `padding` zero bytes past the end.
bytes: [:0]const u8,
/// Where each line begins, the first at zero.
line_starts: []const u32,
tree: AST,

pub const padding = 1;

pub const bytes_max = std.math.maxInt(u32) - padding - 1;

comptime {
    // every token start, span, and line start is a `u32`, so a wider cap would truncate
    assert(bytes_max <= std.math.maxInt(u32));
    assert(bytes_max + padding <= std.math.maxInt(u32));
}

pub const TextError = error{ SourceTooLarge, OutOfMemory };
pub const LoadError = TextError || error{ReadFailed};

/// One-based, in bytes.
pub const LineColumn = struct { line: u32, column: u32 };

const Source = @This();

/// A copy of `text`, for a file with no bytes on disk.
pub fn fromText(gpa: Allocator, path: []const u8, text: []const u8) TextError!Source {
    assert(path.len > 0);
    if (text.len > bytes_max) return error.SourceTooLarge;

    const buffer = try gpa.alloc(u8, text.len + padding);
    errdefer gpa.free(buffer);
    @memcpy(buffer[0..text.len], text);
    @memset(buffer[text.len..], 0);

    return init(gpa, path, buffer[0..text.len :0]);
}

fn read(gpa: Allocator, io: std.Io, path: []const u8) LoadError!Source {
    assert(path.len > 0);

    var file = std.Io.Dir.cwd().openFile(io, path, .{ .mode = .read_only }) catch {
        return error.ReadFailed;
    };
    defer file.close(io);

    const stat = file.stat(io) catch return error.ReadFailed;
    if (stat.size > bytes_max) return error.SourceTooLarge;
    const length: u32 = @intCast(stat.size);

    const buffer = try gpa.alloc(u8, length + padding);
    errdefer gpa.free(buffer);

    var reader = file.reader(io, &.{});
    reader.interface.readSliceAll(buffer[0..length]) catch return error.ReadFailed;
    @memset(buffer[length..], 0);

    return init(gpa, path, buffer[0..length :0]);
}

/// Takes `bytes`, which must carry `padding` zeros past its end.
fn init(gpa: Allocator, path: []const u8, bytes: [:0]const u8) Allocator.Error!Source {
    assert(bytes.len <= bytes_max);

    // guess a line per forty bytes
    var starts: std.ArrayList(u32) = .empty;
    errdefer starts.deinit(gpa);
    try starts.ensureTotalCapacity(gpa, @divFloor(bytes.len, 40) + 2);

    starts.appendAssumeCapacity(0);
    var cursor: u32 = 0;
    while (std.mem.indexOfScalarPos(u8, bytes, cursor, '\n')) |newline| {
        cursor = @intCast(newline + 1);
        try starts.append(gpa, cursor);
    }

    return .{
        .path = path,
        .bytes = bytes,
        .line_starts = try starts.toOwnedSlice(gpa),
        .tree = try AST.parse(gpa, bytes),
    };
}

pub fn deinit(source: *Source, gpa: Allocator) void {
    assert(source.path.len > 0);
    source.tree.deinit(gpa);
    gpa.free(source.bytes.ptr[0 .. source.bytes.len + padding]);
    gpa.free(source.line_starts);
    source.* = undefined;
}

fn lineOf(source: *const Source, offset: u32) u32 {
    assert(offset <= source.bytes.len);
    assert(source.line_starts.len > 0);

    const line = std.sort.upperBound(u32, source.line_starts, offset, order) - 1;
    assert(line < source.line_starts.len);
    assert(source.line_starts[line] <= offset);
    return @intCast(line);
}

pub fn lineColumn(source: *const Source, offset: u32) LineColumn {
    const line = source.lineOf(offset);
    return .{ .line = line + 1, .column = offset - source.line_starts[line] + 1 };
}

/// The text of a one-based line, without its line break.
pub fn lineText(source: *const Source, line: u32) []const u8 {
    if (line == 0 or line > source.line_starts.len) return "";
    return source.lineBytes(line - 1);
}

fn lineBytes(source: *const Source, line: u32) []const u8 {
    const starts = source.line_starts;
    assert(line < starts.len);

    const start = starts[line];
    const end = if (line + 1 < starts.len) starts[line + 1] - 1 else @as(u32, @intCast(source.bytes.len));
    assert(start <= end);

    const text = source.bytes[start..end];
    return if (std.mem.endsWith(u8, text, "\r")) text[0 .. text.len - 1] else text;
}

fn order(offset: u32, start: u32) std.math.Order {
    return std.math.order(offset, start);
}

/// Every source a compilation reads, parsed once and kept by path.
pub const Cache = struct {
    gpa: Allocator,
    io: std.Io,
    map: std.StringHashMapUnmanaged(*Source) = .empty,

    pub fn init(gpa: Allocator, io: std.Io) Cache {
        return .{ .gpa = gpa, .io = io };
    }

    pub fn deinit(cache: *Cache) void {
        var held = cache.map.iterator();
        while (held.next()) |entry| cache.release(entry.key_ptr.*, entry.value_ptr.*);
        cache.map.deinit(cache.gpa);
        cache.* = undefined;
    }

    /// The file at `path`, read from disk unless overlaid, and kept until forgotten.
    pub fn load(cache: *Cache, path: []const u8) LoadError!*const Source {
        assert(path.len > 0);
        if (cache.map.get(path)) |held| return held;
        return cache.keep(path, try read(cache.gpa, cache.io, path));
    }

    /// What `path` reads as from here on. Nothing may still borrow what it replaces.
    pub fn overlay(cache: *Cache, path: []const u8, text: []const u8) TextError!*const Source {
        assert(path.len > 0);
        const source = try fromText(cache.gpa, path, text);
        cache.forget(path);
        return cache.keep(path, source);
    }

    /// The next load reads the disk. Nothing may still borrow what this drops.
    pub fn forget(cache: *Cache, path: []const u8) void {
        assert(path.len > 0);
        const held = cache.map.fetchRemove(path) orelse return;
        cache.release(held.key, held.value);
        assert(cache.map.contains(path) == false);
    }

    fn keep(cache: *Cache, path: []const u8, read_in: Source) Allocator.Error!*const Source {
        assert(cache.map.contains(path) == false);
        const gpa = cache.gpa;
        var source = read_in;
        errdefer source.deinit(gpa);

        const key = try gpa.dupe(u8, path);
        errdefer gpa.free(key);
        source.path = key;

        const held = try gpa.create(Source);
        errdefer gpa.destroy(held);
        held.* = source;

        try cache.map.putNoClobber(gpa, key, held);
        assert(held.tree.nodes.len > 0);
        return held;
    }

    fn release(cache: *Cache, key: []const u8, source: *Source) void {
        // the key is the path the source carries
        assert(source.path.ptr == key.ptr);
        source.deinit(cache.gpa);
        cache.gpa.destroy(source);
        cache.gpa.free(key);
    }
};

const testing = std.testing;

test "an overlay stands in for the disk until it is forgotten" {
    var cache: Cache = .init(testing.allocator, testing.io);
    defer cache.deinit();

    const overlaid = try cache.overlay("lib/std/math.phi", "fn f() {}\n");
    try testing.expectEqual(1, overlaid.tree.viewOf(.root).root.len);
    try testing.expectEqual(overlaid, try cache.load("lib/std/math.phi"));
    try testing.expectEqualStrings("lib/std/math.phi", overlaid.path);

    cache.forget("lib/std/math.phi");
    try testing.expect((try cache.load("lib/std/math.phi")).tree.viewOf(.root).root.len > 1);
    try testing.expectError(error.ReadFailed, cache.load("lib/std/nothing.phi"));
}
