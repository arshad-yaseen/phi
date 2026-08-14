const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const repo_url = "https://github.com/arshad-yaseen/phi";

const fence = "```";
const phi_language = "phi";

const order = [_][]const u8{
    "",
    "language",
};

const walk_depth_max = 8;
const page_bytes_max = 1 << 20;

const Page = struct {
    slug: []const u8,
    url: []const u8,
    title: []const u8,
    description: []const u8,
    text: []const u8,
};

pub fn main(init: std.process.Init) !u8 {
    const arena = init.arena.allocator();
    const io = init.io;

    var log_buffer: [4096]u8 = undefined;
    var log = std.Io.File.stderr().writer(io, &log_buffer);
    defer log.interface.flush() catch {};

    const config = try std.Io.Dir.cwd().readFileAlloc(
        io,
        "zine.ziggy",
        arena,
        .limited(page_bytes_max),
    );
    const title = field(config, ".title") orelse {
        try log.interface.print("generate_llms: zine.ziggy has no .title\n", .{});
        return 1;
    };
    const host = trimRight(field(config, ".host_url") orelse {
        try log.interface.print("generate_llms: zine.ziggy has no .host_url\n", .{});
        return 1;
    }, '/');

    var pages: std.ArrayList(Page) = .empty;
    try collect(arena, io, &pages, "content", "", host, 0);
    std.mem.sort(Page, pages.items, {}, pageBefore);

    var summary: []const u8 = title;
    for (pages.items) |page| {
        if (page.slug.len == 0) summary = page.description;
    }

    var index: Writer.Allocating = .init(arena);
    try writeIndex(&index.writer, title, host, summary, pages.items);
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = "assets/llms.txt",
        .data = index.written(),
    });

    var full: Writer.Allocating = .init(arena);
    try writeFull(&full.writer, title, host, summary, pages.items);
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = "assets/llms-full.txt",
        .data = full.written(),
    });

    for (pages.items) |page| {
        if (rank(page.slug) == order.len) {
            try log.interface.print("note: '{s}' is not in the order, appended at the end\n", .{
                page.slug,
            });
        }
    }
    try log.interface.print("llms.txt       {d} bytes\nllms-full.txt  {d} bytes  ({d} pages)\n", .{
        index.written().len,
        full.written().len,
        pages.items.len,
    });
    return 0;
}

fn collect(
    arena: Allocator,
    io: std.Io,
    pages: *std.ArrayList(Page),
    dir_path: []const u8,
    prefix: []const u8,
    host: []const u8,
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
            const sub_prefix = if (prefix.len == 0)
                name
            else
                try std.fmt.allocPrint(arena, "{s}/{s}", .{ prefix, name });
            try collect(arena, io, pages, sub_path, sub_prefix, host, depth + 1);
            continue;
        }
        if (entry.kind != .file) continue;
        if (std.mem.endsWith(u8, name, ".smd") == false) continue;

        const raw = try std.Io.Dir.cwd().readFileAlloc(
            io,
            sub_path,
            arena,
            .limited(page_bytes_max),
        );
        try pages.append(arena, try read(arena, raw, prefix, name, host));
    }
}

fn read(
    arena: Allocator,
    raw: []const u8,
    prefix: []const u8,
    name: []const u8,
    host: []const u8,
) !Page {
    assert(std.mem.endsWith(u8, name, ".smd"));

    const stem = name[0 .. name.len - ".smd".len];
    const slug = if (std.mem.eql(u8, stem, "index"))
        prefix
    else if (prefix.len == 0)
        stem
    else
        try std.fmt.allocPrint(arena, "{s}/{s}", .{ prefix, stem });

    const body = afterFrontMatter(raw);
    const head = raw[0 .. raw.len - body.len];

    return .{
        .slug = slug,
        .url = if (slug.len == 0)
            try std.fmt.allocPrint(arena, "{s}/", .{host})
        else
            try std.fmt.allocPrint(arena, "{s}/{s}/", .{ host, slug }),
        .title = field(head, ".title") orelse (if (slug.len == 0) "Home" else slug),
        .description = field(head, ".description") orelse "",
        .text = try clean(arena, body, host),
    };
}

fn afterFrontMatter(raw: []const u8) []const u8 {
    if (std.mem.startsWith(u8, raw, "---\n") == false) return raw;
    const close = std.mem.indexOf(u8, raw["---\n".len..], "\n---\n") orelse return raw;
    return raw["---\n".len + close + "\n---\n".len ..];
}

fn field(text: []const u8, name: []const u8) ?[]const u8 {
    assert(name.len > 0);
    assert(name[0] == '.');

    var rest = text;
    while (std.mem.indexOf(u8, rest, name)) |at| {
        rest = rest[at + name.len ..];
        const open = std.mem.indexOfScalar(u8, rest, '"') orelse return null;
        if (std.mem.indexOfScalar(u8, rest[0..open], '\n') != null) continue;
        const close = std.mem.indexOfScalar(u8, rest[open + 1 ..], '"') orelse return null;
        return rest[open + 1 ..][0..close];
    }
    return null;
}

fn clean(arena: Allocator, body: []const u8, host: []const u8) ![]const u8 {
    var out: Writer.Allocating = .init(arena);
    var blank: u32 = 0;
    var code = false;

    var lines = std.mem.splitScalar(u8, body, '\n');
    while (lines.next()) |line| {
        if (std.mem.startsWith(u8, line, fence)) {
            if (code) {
                try out.writer.print("{s}\n", .{fence});
            } else {
                const language = std.mem.trim(u8, line[fence.len..], " \t\r");
                try out.writer.print("{s}{s}\n", .{
                    fence,
                    if (language.len == 0) phi_language else language,
                });
            }
            code = code == false;
            blank = 0;
            continue;
        }
        if (code) {
            try out.writer.print("{s}\n", .{line});
            blank = 0;
            continue;
        }

        const rewritten = try cleanLine(arena, line, host);
        if (std.mem.trim(u8, rewritten, " \t").len == 0) {
            blank += 1;
            if (blank > 1) continue;
        } else {
            blank = 0;
        }
        try out.writer.print("{s}\n", .{rewritten});
    }

    return std.mem.trim(u8, out.written(), "\n");
}

fn cleanLine(arena: Allocator, line: []const u8, host: []const u8) ![]const u8 {
    if (std.mem.startsWith(u8, line, ">[]($block.attrs(")) {
        const open = std.mem.indexOfScalar(u8, line, '\'') orelse return line;
        const close = std.mem.indexOfScalarPos(u8, line, open + 1, '\'') orelse return line;
        const label = line[open + 1 .. close];
        if (label.len == 0) return line;
        return std.fmt.allocPrint(arena, "> **{c}{s}**", .{
            std.ascii.toUpper(label[0]),
            label[1..],
        });
    }

    var out: Writer.Allocating = .init(arena);
    var rest = line;
    while (rest.len > 0) {
        const at = std.mem.indexOfScalar(u8, rest, '[') orelse break;
        const close = std.mem.indexOfScalarPos(u8, rest, at, ']') orelse break;
        if (close + 1 >= rest.len or rest[close + 1] != '(') {
            try out.writer.writeAll(rest[0 .. close + 1]);
            rest = rest[close + 1 ..];
            continue;
        }
        const end = std.mem.indexOfScalarPos(u8, rest, close, ')') orelse break;
        const text = rest[at + 1 .. close];
        const target = rest[close + 2 .. end];

        try out.writer.writeAll(rest[0..at]);
        if (std.mem.startsWith(u8, target, "$")) {
            try out.writer.writeAll(text);
            rest = rest[@min(end + 2, rest.len)..];
            continue;
        }
        if (std.mem.startsWith(u8, target, "/")) {
            try out.writer.print("[{s}]({s}{s})", .{ text, host, target });
        } else {
            try out.writer.print("[{s}]({s})", .{ text, target });
        }
        rest = rest[end + 1 ..];
    }
    try out.writer.writeAll(rest);
    return out.written();
}

fn writeIndex(
    out: *Writer,
    title: []const u8,
    host: []const u8,
    summary: []const u8,
    pages: []const Page,
) !void {
    try out.print("# {s}\n\n> {s}\n\n## Documentation\n\n", .{ title, summary });
    for (pages) |page| {
        try out.print("- [{s}]({s})", .{ page.title, page.url });
        if (page.description.len > 0) try out.print(": {s}", .{page.description});
        try out.writeByte('\n');
    }
    try out.print(
        \\
        \\## Resources
        \\
        \\- [Full documentation text]({s}/llms-full.txt): every page, concatenated
        \\- [Source code]({s})
        \\- [Releases]({s}/releases)
        \\- [Changelog]({s}/blob/main/CHANGELOG.md)
        \\
    , .{ host, repo_url, repo_url, repo_url });
}

fn writeFull(
    out: *Writer,
    title: []const u8,
    host: []const u8,
    summary: []const u8,
    pages: []const Page,
) !void {
    try out.print(
        "# {s}\n\n> {s}\n> Full documentation, every page concatenated for LLMs." ++
            " Index: {s}/llms.txt\n",
        .{ title, summary, host },
    );
    for (pages) |page| {
        try out.print("\n# {s}\n\nSource: {s}\n\n{s}\n", .{ page.title, page.url, page.text });
    }
}

fn rank(slug: []const u8) usize {
    for (order, 0..) |known, at| {
        if (std.mem.eql(u8, known, slug)) return at;
    }
    return order.len;
}

fn pageBefore(_: void, a: Page, b: Page) bool {
    const ra = rank(a.slug);
    const rb = rank(b.slug);
    if (ra != rb) return ra < rb;
    return std.mem.lessThan(u8, a.slug, b.slug);
}

fn trimRight(text: []const u8, byte: u8) []const u8 {
    var end = text.len;
    while (end > 0 and text[end - 1] == byte) end -= 1;
    return text[0..end];
}
