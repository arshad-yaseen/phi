const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const Source = @import("Source.zig");

code: Code,
span: Span,
message: []const u8,
label: []const u8 = "",
help: ?[]const u8 = null,
notes: []const Note = &.{},

pub const Span = struct { start: u32, end: u32 };

pub const Note = struct {
    message: []const u8,
    /// Without one, the note is a bare line.
    span: ?Span = null,
    /// When the span is not in the diagnostic's own file.
    source: ?*const Source = null,
};

pub const Report = struct {
    code: Code,
    message: []const u8,
    label: []const u8 = "",
    help: ?[]const u8 = null,
    notes: []const Note = &.{},
};

/// Parse owns E01xx, analysis E02xx, and the C backend E03xx.
pub const Code = enum(u16) {
    expected_token = 101,
    expected_expression = 102,
    expected_statement = 103,
    expected_declaration = 104,
    expected_parameter = 105,
    expected_struct_member = 106,
    expected_type = 107,
    expected_field_value = 108,
    expected_match_arm = 109,
    chained_comparison = 110,
    invalid_assign_target = 111,
    invalid_bytes = 112,
    stray_else = 113,
    ambiguous_line = 114,
    var_at_top_level = 115,
    extern_fn_body = 116,
    nesting_too_deep = 117,
    too_many_type_params = 118,

    undefined_name = 201,
    redeclared = 202,
    shadows = 203,
    private = 204,
    discard_reserved = 205,
    module_not_found = 206,
    no_prelude_type = 207,
    not_a_type = 208,
    type_as_value = 209,
    not_a_function = 210,
    not_a_union = 211,
    not_a_member = 212,
    not_indexable = 213,
    type_mismatch = 214,
    not_narrowed = 215,
    mixed_types = 216,
    does_not_fit = 217,
    out_of_range = 218,
    bad_operand = 219,
    bad_shift = 220,
    var_needs_type = 221,
    not_constant = 222,
    wrong_arity = 223,
    generic_arguments = 224,
    inference_failed = 225,
    builtin_outside_std = 226,
    extern_signature = 227,
    extern_generic = 228,
    missing_field = 229,
    no_such_member = 230,
    duplicate_member = 231,
    missing_arm = 232,
    duplicate_arm = 233,
    union_too_wide = 234,
    value_unused = 235,
    missing_return = 236,
    outside_loop = 237,
    unreachable_code = 238,
    defer_cannot_leave = 239,
    not_assignable = 240,
    write_through_pointer = 241,
    overflow = 242,
    division_by_zero = 243,
    bad_number = 244,
    bad_text = 245,
    type_too_large = 246,
    size_cycle = 247,
    value_cycle = 248,
    analysis_too_deep = 249,
    instantiates_too_deep = 250,
    compile_error = 251,
    comptime_trapped = 252,
    comptime_too_long = 253,

    entry_signature = 301,
};

comptime {
    // rendered as `E{d:0>4}`, so a wider code would reshape every diagnostic and golden
    for (std.enums.values(Code)) |code| assert(@intFromEnum(code) < 10000);
}

pub const Color = enum { off, on };

/// The nearest of the names offered to a misspelt one, by edit distance.
pub const Closest = struct {
    target: []const u8,
    best: ?[]const u8 = null,
    best_distance: u32 = 3,

    pub fn consider(closest: *Closest, candidate: []const u8) void {
        const found = distance(closest.target, candidate);
        if (found < closest.best_distance) {
            closest.best_distance = found;
            closest.best = candidate;
        }
    }

    pub fn didYouMean(closest: Closest, arena: Allocator) Allocator.Error!?[]const u8 {
        const found = closest.best orelse return null;
        return try std.fmt.allocPrint(arena, "did you mean '{s}'?", .{found});
    }

    /// https://en.wikipedia.org/wiki/Levenshtein_distance
    fn distance(a: []const u8, b: []const u8) u32 {
        const cap = 40;
        const from = a[0..@min(a.len, cap)];
        const to = b[0..@min(b.len, cap)];

        var row: [cap + 1]u32 = undefined;
        for (0..to.len + 1) |column| row[column] = @intCast(column);

        for (from, 1..) |byte, at| {
            var corner = row[0];
            row[0] = @intCast(at);
            for (to, 1..) |other, column| {
                const cost: u32 = if (byte == other) 0 else 1;
                const replaced = corner + cost;
                const inserted = row[column - 1] + 1;
                const removed = row[column] + 1;
                corner = row[column];
                row[column] = @min(replaced, @min(inserted, removed));
            }
        }
        return row[to.len];
    }
};

const Diagnostic = @This();

pub fn render(
    diagnostic: Diagnostic,
    source: *const Source,
    writer: *Writer,
    color: Color,
) Writer.Error!void {
    assert(diagnostic.message.len > 0);
    assert(diagnostic.span.start <= diagnostic.span.end);

    const gutter = diagnostic.gutterWidth(source);
    assert(gutter > 0);

    try writer.print("{s}error[E{d:0>4}]{s}{s}: {s}{s}\n", .{
        tint(color, red),
        @intFromEnum(diagnostic.code),
        tint(color, reset),
        tint(color, bold),
        diagnostic.message,
        tint(color, reset),
    });
    try renderSnippet(source, writer, color, gutter, diagnostic.span, diagnostic.label, red);

    if (diagnostic.help) |help| {
        assert(help.len > 0);
        try renderGutter(writer, color, gutter, null);
        try writer.writeByte('\n');
        try writer.splatByteAll(' ', gutter);
        try writer.print(" {s}= help{s}: {s}\n", .{ tint(color, blue), tint(color, reset), help });
    }

    for (diagnostic.notes) |note| {
        assert(note.message.len > 0);
        try writer.print("{s}note{s}{s}: {s}{s}\n", .{
            tint(color, blue),
            tint(color, reset),
            tint(color, bold),
            note.message,
            tint(color, reset),
        });
        if (note.span) |span| {
            const where = note.source orelse source;
            try renderSnippet(where, writer, color, gutter, span, "", blue);
        }
    }

    try writer.writeByte('\n');
}

fn gutterWidth(diagnostic: Diagnostic, source: *const Source) u32 {
    var widest = source.lineColumn(diagnostic.span.start).line;
    assert(widest > 0);

    for (diagnostic.notes) |note| {
        if (note.span) |span| {
            const noted = note.source orelse source;
            widest = @max(widest, noted.lineColumn(span.start).line);
        }
    }
    return digits(widest);
}

fn renderSnippet(
    source: *const Source,
    writer: *Writer,
    color: Color,
    gutter: u32,
    span: Span,
    label: []const u8,
    caret_color: []const u8,
) Writer.Error!void {
    assert(span.start <= span.end);

    const location = source.lineColumn(span.start);
    const text = source.lineText(location.line);
    assert(location.column > 0);

    try writer.splatByteAll(' ', gutter);
    try writer.print("{s}-->{s} {s}:{d}:{d}\n", .{
        tint(color, blue), tint(color, reset), source.path, location.line, location.column,
    });

    try renderGutter(writer, color, gutter, null);
    try writer.writeByte('\n');

    try renderGutter(writer, color, gutter, location.line);
    if (text.len > 0) {
        try writer.writeByte(' ');
        try writeSourceLine(writer, text);
    }
    try writer.writeByte('\n');

    const indent = location.column - 1;
    const to_line_end: u32 = if (indent < text.len) @intCast(text.len - indent) else 0;
    const carets = @max(1, @min(span.end -| span.start, to_line_end));

    try renderGutter(writer, color, gutter, null);
    try writer.writeByte(' ');
    try writer.splatByteAll(' ', indent);
    try writer.writeAll(tint(color, caret_color));
    try writer.splatByteAll('^', carets);
    if (label.len > 0) {
        try writer.writeByte(' ');
        try writer.writeAll(label);
    }
    try writer.print("{s}\n", .{tint(color, reset)});
}

fn renderGutter(writer: *Writer, color: Color, gutter: u32, line: ?u32) Writer.Error!void {
    assert(gutter > 0);

    if (line) |number| {
        assert(digits(number) <= gutter);
        try writer.splatByteAll(' ', gutter - digits(number));
        try writer.print("{s}{d} |{s}", .{ tint(color, blue), number, tint(color, reset) });
    } else {
        try writer.splatByteAll(' ', gutter);
        try writer.print(" {s}|{s}", .{ tint(color, blue), tint(color, reset) });
    }
}

fn writeSourceLine(writer: *Writer, text: []const u8) Writer.Error!void {
    assert(std.mem.indexOfScalar(u8, text, '\n') == null);
    for (text) |byte| try writer.writeByte(if (byte < 0x20 or byte == 0x7F) ' ' else byte);
}

fn digits(line: u32) u32 {
    assert(line > 0);
    return std.math.log10_int(line) + 1;
}

const red = "\x1b[1;31m";
const blue = "\x1b[1;34m";
const bold = "\x1b[1m";
const reset = "\x1b[0m";

fn tint(color: Color, escape: []const u8) []const u8 {
    assert(escape.len > 0);
    return switch (color) {
        .on => escape,
        .off => "",
    };
}

const testing = std.testing;

fn expectRender(text: []const u8, diagnostic: Diagnostic, want: []const u8) !void {
    var source: Source = try .fromText(testing.allocator, "demo.phi", text);
    defer source.deinit(testing.allocator);

    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();

    try diagnostic.render(&source, &out.writer, .off);
    try testing.expectEqualStrings(want, out.written());
}

test "header, arrow, gutter, source line, carets, label" {
    try expectRender("let x = 1\nlet y = 2\n", .{
        .code = .expected_token,
        .span = .{ .start = 16, .end = 17 },
        .message = "expected ':', found '='",
        .label = "here",
    },
        \\error[E0101]: expected ':', found '='
        \\ --> demo.phi:2:7
        \\  |
        \\2 | let y = 2
        \\  |       ^ here
        \\
        \\
    );
}

test "help and a note with its own snippet" {
    try expectRender("f(a\n  b)\n", .{
        .code = .expected_token,
        .span = .{ .start = 6, .end = 7 },
        .message = "expected ')', found an identifier",
        .label = "expected ')'",
        .help = "arguments are separated by ','",
        .notes = &.{.{
            .message = "to match this '('",
            .span = .{ .start = 1, .end = 2 },
        }},
    },
        \\error[E0101]: expected ')', found an identifier
        \\ --> demo.phi:2:3
        \\  |
        \\2 |   b)
        \\  |   ^ expected ')'
        \\  |
        \\  = help: arguments are separated by ','
        \\note: to match this '('
        \\ --> demo.phi:1:2
        \\  |
        \\1 | f(a
        \\  |  ^
        \\
        \\
    );
}

test "one gutter width covers the widest line the diagnostic shows" {
    try expectRender("\n\n\n\n\n\n\n\n\nbad\n", .{
        .code = .invalid_bytes,
        .span = .{ .start = 9, .end = 12 },
        .message = "invalid bytes",
        .notes = &.{.{ .message = "the file starts here", .span = .{ .start = 0, .end = 1 } }},
    },
        \\error[E0112]: invalid bytes
        \\  --> demo.phi:10:1
        \\   |
        \\10 | bad
        \\   | ^^^
        \\note: the file starts here
        \\  --> demo.phi:1:1
        \\   |
        \\ 1 |
        \\   | ^
        \\
        \\
    );
}

test "a span past the end of its line still renders one caret" {
    try expectRender("ab", .{
        .code = .expected_token,
        .span = .{ .start = 2, .end = 2 },
        .message = "expected ';', found end of file",
    },
        \\error[E0101]: expected ';', found end of file
        \\ --> demo.phi:1:3
        \\  |
        \\1 | ab
        \\  |   ^
        \\
        \\
    );
}

test "color wraps the pieces without moving them" {
    var source: Source = try .fromText(testing.allocator, "d.phi", "ab\n");
    defer source.deinit(testing.allocator);

    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();

    const diagnostic: Diagnostic = .{
        .code = .invalid_bytes,
        .span = .{ .start = 0, .end = 1 },
        .message = "m",
    };
    try diagnostic.render(&source, &out.writer, .on);
    try testing.expectEqualStrings(
        "\x1b[1;31merror[E0112]\x1b[0m\x1b[1m: m\x1b[0m\n" ++
            " \x1b[1;34m-->\x1b[0m d.phi:1:1\n" ++
            "  \x1b[1;34m|\x1b[0m\n" ++
            "\x1b[1;34m1 |\x1b[0m ab\n" ++
            "  \x1b[1;34m|\x1b[0m \x1b[1;31m^\x1b[0m\n\n",
        out.written(),
    );
}
