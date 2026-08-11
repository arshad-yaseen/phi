const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const Source = @import("Source.zig");

code: Code,
/// What the carets sit under.
span: Span,
/// The header line.
message: []const u8,
/// Beside the carets.
label: []const u8 = "",
help: ?[]const u8 = null,
/// Each renders its own snippet.
notes: []const Note = &.{},

pub const Span = struct { start: u32, end: u32 };

pub const Note = struct {
    message: []const u8,
    /// Without one, the note is a bare line.
    span: ?Span = null,
    /// When the span is not in the diagnostic's own file.
    source: ?*Source = null,
};

/// Parse owns E01xx, analysis E02xx.
pub const Code = enum(u16) {
    expected_token = 101,
    expected_expression = 102,
    expected_statement = 103,
    expected_declaration = 104,
    expected_parameter = 105,
    expected_struct_member = 106,
    expected_type = 107,
    expected_field_value = 108,
    chained_comparison = 109,
    invalid_assign_target = 110,
    nesting_too_deep = 111,
    invalid_bytes = 112,
    stray_else = 113,
    var_at_top_level = 116,
    ambiguous_line = 117,
    too_many_type_params = 118,
    expected_match_arm = 119,

    undefined_name = 201,
    not_a_type = 202,
    type_as_value = 203,
    redeclared = 204,
    shadows = 205,
    type_mismatch = 206,
    mixed_types = 207,
    does_not_fit = 208,
    overflow = 209,
    division_by_zero = 210,
    bad_operand = 211,
    not_a_function = 212,
    wrong_arity = 213,
    not_constant = 214,
    var_needs_type = 215,
    missing_field = 218,
    no_such_member = 219,
    private = 220,
    not_assignable = 221,
    write_through_pointer = 222,
    value_unused = 230,
    missing_return = 231,
    outside_loop = 232,
    size_cycle = 233,
    value_cycle = 234,
    module_not_found = 235,
    instantiates_too_deep = 241,
    inference_failed = 242,
    discard_reserved = 244,
    defer_cannot_leave = 245,
    generic_arguments = 246,
    bad_number = 247,
    analysis_too_deep = 249,
    unreachable_code = 250,
    builtin_outside_std = 251,
    not_indexable = 252,
    bad_shift = 253,
    duplicate_member = 254,
    union_too_wide = 255,
    not_a_union = 256,
    not_a_member = 257,
    no_prelude_type = 258,
    missing_arm = 259,
    duplicate_arm = 260,
    type_too_large = 261,
    out_of_range = 262,
    bad_text = 263,
};

comptime {
    // rendered as `E{d:0>4}`, so a wider code would reshape every diagnostic and golden
    for (std.enums.values(Code)) |code| assert(@intFromEnum(code) < 10000);
}

pub const Color = enum { off, on };

pub const RenderError = Allocator.Error || Writer.Error;

const Diagnostic = @This();

pub fn render(
    diagnostic: Diagnostic,
    gpa: Allocator,
    source: *Source,
    writer: *Writer,
    color: Color,
) RenderError!void {
    assert(diagnostic.message.len > 0);
    assert(diagnostic.span.start <= diagnostic.span.end);

    const gutter = try diagnostic.gutterWidth(gpa, source);
    assert(gutter > 0);

    try writer.print("{s}error[E{d:0>4}]{s}{s}: {s}{s}\n", .{
        tint(color, red),
        @intFromEnum(diagnostic.code),
        tint(color, reset),
        tint(color, bold),
        diagnostic.message,
        tint(color, reset),
    });
    try renderSnippet(gpa, source, writer, color, gutter, diagnostic.span, diagnostic.label, red);

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
            try renderSnippet(gpa, where, writer, color, gutter, span, "", blue);
        }
    }

    try writer.writeByte('\n');
}

fn gutterWidth(diagnostic: Diagnostic, gpa: Allocator, source: *Source) Allocator.Error!u32 {
    var widest = (try source.lineColumn(gpa, diagnostic.span.start)).line;
    assert(widest > 0);

    for (diagnostic.notes) |note| {
        if (note.span) |span| {
            const noted = note.source orelse source;
            const line = (try noted.lineColumn(gpa, span.start)).line;
            widest = @max(widest, line);
        }
    }
    return digits(widest);
}

fn renderSnippet(
    gpa: Allocator,
    source: *Source,
    writer: *Writer,
    color: Color,
    gutter: u32,
    span: Span,
    label: []const u8,
    caret_color: []const u8,
) RenderError!void {
    assert(span.start <= span.end);

    const location = try source.lineColumn(gpa, span.start);
    const text = try source.lineText(gpa, location.line);
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

fn expectRender(text: [:0]const u8, diagnostic: Diagnostic, want: []const u8) !void {
    var source: Source = .{ .path = "demo.phi", .bytes = text };
    defer if (source.line_starts) |starts| testing.allocator.free(starts);

    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();

    try diagnostic.render(testing.allocator, &source, &out.writer, .off);
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
    var source: Source = .{ .path = "d.phi", .bytes = "ab\n" };
    defer if (source.line_starts) |starts| testing.allocator.free(starts);

    var out: Writer.Allocating = .init(testing.allocator);
    defer out.deinit();

    const diagnostic: Diagnostic = .{
        .code = .invalid_bytes,
        .span = .{ .start = 0, .end = 1 },
        .message = "m",
    };
    try diagnostic.render(testing.allocator, &source, &out.writer, .on);
    try testing.expectEqualStrings(
        "\x1b[1;31merror[E0112]\x1b[0m\x1b[1m: m\x1b[0m\n" ++
            " \x1b[1;34m-->\x1b[0m d.phi:1:1\n" ++
            "  \x1b[1;34m|\x1b[0m\n" ++
            "\x1b[1;34m1 |\x1b[0m ab\n" ++
            "  \x1b[1;34m|\x1b[0m \x1b[1;31m^\x1b[0m\n\n",
        out.written(),
    );
}
