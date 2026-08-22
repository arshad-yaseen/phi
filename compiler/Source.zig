const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

path: []const u8,
/// The file, with `padding` zero bytes past the end.
bytes: [:0]const u8,
line_starts: ?[]u32 = null,

pub const padding = 1;

pub const bytes_max = std.math.maxInt(u32) - padding - 1;

comptime {
    // every token start, span, and line start is a `u32`, so a wider cap would truncate
    assert(bytes_max <= std.math.maxInt(u32));
    assert(bytes_max + padding <= std.math.maxInt(u32));
}

pub const LoadError = error{ SourceTooLarge, OutOfMemory, ReadFailed };

pub const LineColumn = struct { line: u32, column: u32 };

const Source = @This();

pub fn load(gpa: Allocator, io: std.Io, dir: std.Io.Dir, path: []const u8) LoadError!Source {
    assert(path.len > 0);

    var file = dir.openFile(io, path, .{ .mode = .read_only }) catch return error.ReadFailed;
    defer file.close(io);

    const stat = file.stat(io) catch return error.ReadFailed;
    if (stat.size > bytes_max) return error.SourceTooLarge;
    const length: u32 = @intCast(stat.size);

    const buffer = try gpa.alloc(u8, length + padding);
    errdefer gpa.free(buffer);

    var reader = file.reader(io, &.{});
    reader.interface.readSliceAll(buffer[0..length]) catch return error.ReadFailed;
    @memset(buffer[length..], 0);

    assert(buffer.len == length + padding);
    return .{ .path = path, .bytes = buffer[0..length :0] };
}

pub fn deinit(source: *Source, gpa: Allocator) void {
    assert(source.path.len > 0);
    gpa.free(source.bytes.ptr[0 .. source.bytes.len + padding]);
    if (source.line_starts) |starts| gpa.free(starts);
    source.* = undefined;
}

pub fn lineColumn(source: *Source, gpa: Allocator, offset: u32) Allocator.Error!LineColumn {
    assert(offset <= source.bytes.len);

    const starts = try source.lineStarts(gpa);
    assert(starts.len > 0);

    const line_index = std.sort.upperBound(u32, starts, offset, order) - 1;
    assert(line_index < starts.len);
    assert(starts[line_index] <= offset);

    return .{ .line = @intCast(line_index + 1), .column = offset - starts[line_index] + 1 };
}

pub fn lineText(source: *Source, gpa: Allocator, line: u32) Allocator.Error![]const u8 {
    const starts = try source.lineStarts(gpa);
    if (line == 0 or line > starts.len) return "";

    const start = starts[line - 1];
    const end = if (line < starts.len) starts[line] - 1 else @as(u32, @intCast(source.bytes.len));
    assert(start <= end);

    const text = source.bytes[start..end];
    return if (std.mem.endsWith(u8, text, "\r")) text[0 .. text.len - 1] else text;
}

fn lineStarts(source: *Source, gpa: Allocator) Allocator.Error![]u32 {
    if (source.line_starts) |starts| return starts;

    // guess a line per forty bytes
    var starts: std.ArrayList(u32) = .empty;
    errdefer starts.deinit(gpa);
    try starts.ensureTotalCapacity(gpa, @divFloor(source.bytes.len, 40) + 2);

    starts.appendAssumeCapacity(0);
    var cursor: u32 = 0;
    while (std.mem.indexOfScalarPos(u8, source.bytes, cursor, '\n')) |newline| {
        cursor = @intCast(newline + 1);
        try starts.append(gpa, cursor);
    }

    const owned = try starts.toOwnedSlice(gpa);
    source.line_starts = owned;
    return owned;
}

fn order(offset: u32, start: u32) std.math.Order {
    return std.math.order(offset, start);
}
