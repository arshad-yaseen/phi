const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const fence = "```";

const work_dir = ".snippets";

const skipped = [_][]const u8{};

const walk_depth_max = 8;
const page_bytes_max = 1 << 20;

pub fn main(init: std.process.Init) !u8 {
    const arena = init.arena.allocator();
    const io = init.io;

    var log_buffer: [4096]u8 = undefined;
    var log = std.Io.File.stderr().writer(io, &log_buffer);
    defer log.interface.flush() catch {};

    var phi_path: []const u8 = "../zig-out/bin/phi";
    var std_dir: []const u8 = "../lib/std";

    const args = try init.minimal.args.toSlice(arena);
    var at: usize = 1;
    while (at < args.len) : (at += 1) {
        const wants_value = at + 1 < args.len;
        if (std.mem.eql(u8, args[at], "--phi") and wants_value) {
            at += 1;
            phi_path = args[at];
            continue;
        }
        if (std.mem.eql(u8, args[at], "--std") and wants_value) {
            at += 1;
            std_dir = args[at];
            continue;
        }
        try log.interface.print("usage: check_snippets [--phi <path>] [--std <dir>]\n", .{});
        return 2;
    }

    var pages: std.ArrayList([]const u8) = .empty;
    try collect(arena, io, &pages, "content", 0);
    std.mem.sort([]const u8, pages.items, {}, stringBefore);

    var checked: u32 = 0;
    var failures: u32 = 0;
    for (pages.items) |page| {
        const result = try checkPage(arena, io, page, phi_path, std_dir, &log.interface);
        checked += result.checked;
        failures += result.failures;
    }

    std.Io.Dir.cwd().deleteTree(io, work_dir) catch {};

    assert(checked >= failures);
    if (failures > 0) {
        try log.interface.print("{d} of {d} snippets failed\n", .{ failures, checked });
        return 1;
    }
    try log.interface.print("{d} snippets check clean\n", .{checked});
    return 0;
}

const Result = struct { checked: u32, failures: u32 };

fn checkPage(
    arena: Allocator,
    io: std.Io,
    page: []const u8,
    phi_path: []const u8,
    std_dir: []const u8,
    log: *Writer,
) !Result {
    assert(std.mem.startsWith(u8, page, "content/"));
    const key = page["content/".len..];
    const text = try std.Io.Dir.cwd().readFileAlloc(io, page, arena, .limited(page_bytes_max));

    var result: Result = .{ .checked = 0, .failures = 0 };
    var project: ?[]const u8 = null;
    var first: u32 = 0;

    var rest: []const u8 = text;
    var number: u32 = 0;
    while (nextBlock(&rest)) |block| {
        if (block.language.len > 0) continue;
        number += 1;

        const name = headerOf(block.body);
        if (project != null and name == null) {
            try run(arena, io, project.?, phi_path, std_dir, key, first, log, &result);
            project = null;
        }
        if (isSkipped(key, number)) continue;

        if (name) |file| {
            if (project == null) {
                try reset(io);
                first = number;
                project = try std.fmt.allocPrint(arena, "{s}/{s}", .{ work_dir, file });
            }
            const path = try std.fmt.allocPrint(arena, "{s}/{s}", .{ work_dir, file });
            try writeUnder(io, path, block.body);
            if (std.mem.endsWith(u8, file, "main.phi")) project = path;
            continue;
        }

        try reset(io);
        const path = work_dir ++ "/snippet.phi";
        try writeUnder(io, path, block.body);
        try run(arena, io, path, phi_path, std_dir, key, number, log, &result);
    }
    if (project) |entry| {
        try run(arena, io, entry, phi_path, std_dir, key, first, log, &result);
    }
    return result;
}

const Block = struct { language: []const u8, body: []const u8 };

fn nextBlock(rest: *[]const u8) ?Block {
    while (rest.len > 0) {
        const line = nextLine(rest);
        if (std.mem.startsWith(u8, line, fence) == false) continue;

        const language = std.mem.trim(u8, line[fence.len..], " \t\r");
        const body = rest.*;
        var len: usize = 0;
        while (rest.len > 0) {
            const before = rest.len;
            if (std.mem.startsWith(u8, nextLine(rest), fence)) break;
            len += before - rest.len;
        }
        return .{ .language = language, .body = body[0..len] };
    }
    return null;
}

fn nextLine(rest: *[]const u8) []const u8 {
    const end = std.mem.indexOfScalar(u8, rest.*, '\n') orelse rest.len;
    const line = rest.*[0..end];
    rest.* = rest.*[@min(end + 1, rest.len)..];
    return line;
}

fn headerOf(block: []const u8) ?[]const u8 {
    if (std.mem.startsWith(u8, block, "// ") == false) return null;
    const line_end = std.mem.indexOfScalar(u8, block, '\n') orelse return null;
    const name = block["// ".len..line_end];
    if (std.mem.endsWith(u8, name, ".phi") == false) return null;
    if (std.mem.indexOfScalar(u8, name, ' ') != null) return null;
    return name;
}

fn isSkipped(key: []const u8, number: u32) bool {
    var buffer: [128]u8 = undefined;
    const written = std.fmt.bufPrint(&buffer, "{s}:{d}", .{ key, number }) catch return false;
    for (skipped) |known| {
        if (std.mem.eql(u8, known, written)) return true;
    }
    return false;
}

fn run(
    arena: Allocator,
    io: std.Io,
    entry: []const u8,
    phi_path: []const u8,
    std_dir: []const u8,
    key: []const u8,
    number: u32,
    log: *Writer,
    result: *Result,
) !void {
    result.checked += 1;

    const done = try std.process.run(arena, io, .{
        .argv = &.{ phi_path, "check", entry, "--std", std_dir, "--color", "off" },
        .stderr_limit = .limited(page_bytes_max),
        .stdout_limit = .limited(page_bytes_max),
    });

    const clean = switch (done.term) {
        .exited => |code| code == 0,
        else => false,
    };
    if (clean) return;

    result.failures += 1;
    try log.print("{s} block {d}:\n{s}\n", .{ key, number, done.stderr });
}

fn writeUnder(io: std.Io, path: []const u8, text: []const u8) !void {
    assert(std.mem.startsWith(u8, path, work_dir));

    if (std.fs.path.dirname(path)) |parent| {
        try std.Io.Dir.cwd().createDirPath(io, parent);
    }
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = path, .data = text });
}

fn reset(io: std.Io) !void {
    std.Io.Dir.cwd().deleteTree(io, work_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, work_dir);
}

fn collect(
    arena: Allocator,
    io: std.Io,
    pages: *std.ArrayList([]const u8),
    dir_path: []const u8,
    depth: u32,
) !void {
    assert(dir_path.len > 0);
    assert(depth < walk_depth_max);

    var dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer dir.close(io);

    var walk = dir.iterate();
    while (try walk.next(io)) |entry| {
        const name = try arena.dupe(u8, entry.name);
        const sub_path = try std.fmt.allocPrint(arena, "{s}/{s}", .{ dir_path, name });

        if (entry.kind == .directory) {
            try collect(arena, io, pages, sub_path, depth + 1);
            continue;
        }
        if (entry.kind != .file) continue;
        if (std.mem.endsWith(u8, name, ".smd") == false) continue;
        try pages.append(arena, sub_path);
    }
}

fn stringBefore(_: void, a: []const u8, b: []const u8) bool {
    return std.mem.lessThan(u8, a, b);
}
