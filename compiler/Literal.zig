const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const Diagnostic = @import("Diagnostic.zig");

pub const Refusal = Diagnostic.Report;

pub const Decoded = union(enum) {
    int: i128,
    float: f64,
    refused: Refusal,
};

pub fn decodeNumber(arena: Allocator, text: []const u8) Allocator.Error!Decoded {
    assert(text.len > 0);

    // most literals are plain decimals, and 18 digits cannot overflow
    if (text.len <= 18) fast: {
        if (text.len > 1 and text[0] == '0') break :fast;
        var value: i128 = 0;
        for (text) |byte| {
            if (byte < '0') break :fast;
            if (byte > '9') break :fast;
            value = value * 10 + (byte - '0');
        }
        return .{ .int = value };
    }
    return decodeSlow(arena, text);
}

fn decodeSlow(arena: Allocator, text: []const u8) Allocator.Error!Decoded {
    switch (std.zig.parseNumberLiteral(text)) {
        .int => |value| return .{ .int = value },
        .big_int => |base| return decodeWide(text, base),
        .float => {
            const value = std.fmt.parseFloat(f64, text) catch {
                return .{ .refused = try refusalOf(arena, text, .{ .invalid_character = 0 }) };
            };
            if (std.math.isFinite(value) == false) {
                return .{ .refused = .{
                    .code = .bad_number,
                    .message = "this number is too large for a float",
                    .label = "does not fit",
                } };
            }
            return .{ .float = value };
        },
        .failure => |failure| return .{ .refused = try refusalOf(arena, text, failure) },
    }
}

fn decodeWide(text: []const u8, base: std.zig.number_literal.Base) Decoded {
    const radix: u8 = @intFromEnum(base);
    const digits = if (base == .decimal) text else text[2..];

    var value: i128 = 0;
    for (digits) |byte| {
        const digit = std.fmt.charToDigit(byte, radix) catch continue;
        const wide = std.math.mul(i128, value, radix) catch return too_wide;
        value = std.math.add(i128, wide, digit) catch return too_wide;
    }
    return .{ .int = value };
}

const too_wide: Decoded = .{ .refused = .{
    .code = .bad_number,
    .message = "this number needs more than 128 bits, the width constants fold in",
    .label = "too large",
} };

fn refusalOf(
    arena: Allocator,
    text: []const u8,
    failure: std.zig.number_literal.Error,
) Allocator.Error!Refusal {
    return switch (failure) {
        .leading_zero => .{
            .code = .bad_number,
            .message = "a decimal number cannot start with zero",
            .label = "leading zero",
            .help = "write the '0o' prefix if octal was meant, or drop the zero",
        },
        .digit_after_base => .{
            .code = .bad_number,
            .message = "a base prefix needs digits after it",
            .label = "no digits",
        },
        .upper_case_base => .{
            .code = .bad_number,
            .message = "a base prefix is lowercase: '0x', '0o', or '0b'",
            .label = "uppercase prefix",
        },
        .invalid_float_base => .{
            .code = .bad_number,
            .message = "a float is decimal, or hex with a 'p' exponent",
            .label = "wrong base for a float",
        },
        .repeated_underscore,
        .invalid_underscore_after_special,
        .trailing_underscore,
        .exponent_after_underscore,
        .special_after_underscore,
        => .{
            .code = .bad_number,
            .message = "'_' separates digits, so one sits between two of them",
            .label = "misplaced '_'",
        },
        .invalid_digit => |info| .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(arena, "'{c}' is not a {t} digit", .{
                text[info.i], info.base,
            }),
            .label = "not a digit",
        },
        .invalid_digit_exponent => |at| .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(arena, "'{c}' is not a digit an exponent takes", .{
                text[at],
            }),
            .label = "not an exponent digit",
        },
        .duplicate_period => .{
            .code = .bad_number,
            .message = "a number holds one '.'",
            .label = "a second '.'",
        },
        .duplicate_exponent => .{
            .code = .bad_number,
            .message = "a number holds one exponent",
            .label = "a second exponent",
        },
        .trailing_special => .{
            .code = .bad_number,
            .message = "this number ends before its digits do",
            .label = "digits expected after this",
        },
        .invalid_exponent_sign => |at| .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(
                arena,
                "a sign continues an exponent, and '{c}' follows a digit",
                .{text[at]},
            ),
            .label = "misplaced sign",
        },
        .period_after_exponent => .{
            .code = .bad_number,
            .message = "an exponent holds no '.'",
            .label = "'.' in an exponent",
        },
        .invalid_character => .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(arena, "'{s}' is not a number the language knows", .{
                text,
            }),
            .label = "unreadable",
            .help = "numbers are decimal, hex '0x', octal '0o', or binary '0b', " ++
                "with '.' and 'e' for floats",
        },
    };
}

const codepoint_max = 0x10FFFF;

pub const Char = union(enum) { codepoint: u32, refused: Refusal };

pub const Piece = union(enum) { bytes: []const u8, refused: Refusal };

pub const Bytes = struct {
    text: []const u8,
    cursor: u32,
    /// Staging for an escape, four being the widest UTF-8 sequence.
    encoded: [4]u8,
    stopped: bool,

    pub fn next(reading: *Bytes) ?Piece {
        assert(reading.cursor >= 1);
        assert(reading.cursor <= reading.text.len);
        if (reading.stopped) return null;

        if (reading.cursor == reading.text.len) return reading.stop(string_cut);

        switch (reading.text[reading.cursor]) {
            '"' => {
                reading.stopped = true;
                return null;
            },
            '\\' => {
                // a trailing backslash means the closing quote is what went missing
                if (reading.cursor + 1 == reading.text.len) return reading.stop(string_cut);
                switch (escapeAt(reading.text, reading.cursor)) {
                    .refused => |refusal| return reading.stop(refusal),
                    .unit => |unit| {
                        reading.cursor += unit.width;
                        return reading.encode(unit.value);
                    },
                }
            },
            else => {
                const from = reading.cursor;
                while (reading.cursor < reading.text.len) : (reading.cursor += 1) {
                    const byte = reading.text[reading.cursor];
                    if (byte == '"') break;
                    if (byte == '\\') break;
                }
                assert(reading.cursor > from);
                return .{ .bytes = reading.text[from..reading.cursor] };
            },
        }
    }

    fn stop(reading: *Bytes, refusal: Refusal) Piece {
        assert(reading.stopped == false);
        reading.stopped = true;
        return .{ .refused = refusal };
    }

    fn encode(reading: *Bytes, value: Unit.Value) Piece {
        switch (value) {
            .byte => |byte| {
                reading.encoded[0] = byte;
                return .{ .bytes = reading.encoded[0..1] };
            },
            .codepoint => |codepoint| {
                const width = std.unicode.utf8Encode(codepoint, &reading.encoded) catch |err| {
                    return reading.stop(switch (err) {
                        error.Utf8CannotEncodeSurrogateHalf => surrogate,
                        error.CodepointTooLarge => codepoint_too_large,
                    });
                };
                return .{ .bytes = reading.encoded[0..width] };
            },
        }
    }
};

pub fn bytesOf(literal: []const u8) Bytes {
    assert(literal.len > 0);
    assert(literal[0] == '"');
    return .{ .text = literal, .cursor = 1, .encoded = @splat(0), .stopped = false };
}

pub fn textLine(line: []const u8) []const u8 {
    assert(line.len >= 2);
    assert(line[0] == '\\');
    assert(line[1] == '\\');

    const written = line[2..];

    if (std.mem.endsWith(u8, written, "\r")) return written[0 .. written.len - 1];
    return written;
}

pub fn decodeChar(literal: []const u8) Char {
    assert(literal.len > 0);
    assert(literal[0] == '\'');

    // two bytes are the empty literal, and anything shorter never closed
    if (literal.len < 3) {
        if (literal.len == 2 and literal[1] == '\'') return .{ .refused = char_empty };
        return .{ .refused = char_cut };
    }
    if (literal[1] == '\'') return .{ .refused = char_empty };

    const read = if (literal[1] == '\\') escapeAt(literal, 1) else utf8At(literal, 1);
    const unit = switch (read) {
        .refused => |refusal| return .{ .refused = refusal },
        .unit => |found| found,
    };

    const end = 1 + unit.width;
    if (end >= literal.len) return .{ .refused = char_cut };
    if (literal[end] != '\'') return .{ .refused = char_crowded };

    // the token ends at the first quote the body did not escape
    assert(end + 1 == literal.len);
    return .{ .codepoint = switch (unit.value) {
        .byte => |byte| byte,
        .codepoint => |codepoint| codepoint,
    } };
}

const Unit = struct {
    value: Value,
    width: u32,

    const Value = union(enum) { byte: u8, codepoint: u21 };
};

const Read = union(enum) { unit: Unit, refused: Refusal };

fn escapeAt(literal: []const u8, at: u32) Read {
    assert(literal[at] == '\\');
    assert(at + 1 < literal.len);

    return switch (literal[at + 1]) {
        'n' => oneByte('\n'),
        'r' => oneByte('\r'),
        't' => oneByte('\t'),
        '\\' => oneByte('\\'),
        '\'' => oneByte('\''),
        '"' => oneByte('"'),
        'x' => byteEscape(literal, at),
        'u' => codepointEscape(literal, at),
        else => .{ .refused = unknown_escape },
    };
}

/// A backslash and one letter, so every one of them is two bytes wide.
fn oneByte(value: u8) Read {
    return .{ .unit = .{ .value = .{ .byte = value }, .width = 2 } };
}

fn byteEscape(literal: []const u8, at: u32) Read {
    assert(literal[at] == '\\');
    assert(literal[at + 1] == 'x');

    const digits = at + 2;
    if (digits + 2 > literal.len) return .{ .refused = bad_byte_escape };

    const high = std.fmt.charToDigit(literal[digits], 16) catch
        return .{ .refused = bad_byte_escape };
    const low = std.fmt.charToDigit(literal[digits + 1], 16) catch
        return .{ .refused = bad_byte_escape };

    return .{ .unit = .{ .value = .{ .byte = high * 16 + low }, .width = 4 } };
}

fn codepointEscape(literal: []const u8, at: u32) Read {
    assert(literal[at] == '\\');
    assert(literal[at + 1] == 'u');

    // six digits reach the last codepoint, and a seventh could only be past it
    const digits_max = 6;

    if (at + 2 == literal.len) return .{ .refused = bad_codepoint_escape };
    if (literal[at + 2] != '{') return .{ .refused = bad_codepoint_escape };

    var value: u32 = 0;
    var count: u32 = 0;
    var cursor = at + 3;
    while (cursor < literal.len and literal[cursor] != '}') : (cursor += 1) {
        if (count == digits_max) return .{ .refused = codepoint_too_large };
        const digit = std.fmt.charToDigit(literal[cursor], 16) catch
            return .{ .refused = bad_codepoint_escape };
        value = value * 16 + digit;
        count += 1;
    }
    if (cursor == literal.len) return .{ .refused = bad_codepoint_escape };
    if (count == 0) return .{ .refused = bad_codepoint_escape };

    assert(literal[cursor] == '}');
    if (value > codepoint_max) return .{ .refused = codepoint_too_large };
    // half of a surrogate pair is not a codepoint, so nothing encodes it
    if (value >= 0xD800 and value <= 0xDFFF) return .{ .refused = surrogate };
    return .{ .unit = .{ .value = .{ .codepoint = @intCast(value) }, .width = cursor + 1 - at } };
}

fn utf8At(literal: []const u8, at: u32) Read {
    assert(at > 0);
    assert(at < literal.len);

    const width = std.unicode.utf8ByteSequenceLength(literal[at]) catch
        return .{ .refused = bad_utf8 };
    if (at + width > literal.len) return .{ .refused = bad_utf8 };

    const value = std.unicode.utf8Decode(literal[at..][0..width]) catch
        return .{ .refused = bad_utf8 };
    return .{ .unit = .{ .value = .{ .codepoint = value }, .width = width } };
}

const escapes_help = "the escapes are '\\n', '\\r', '\\t', '\\\\', '\\'', '\\\"', " ++
    "'\\xNN' for a byte, and '\\u{...}' for a codepoint";

const string_cut: Refusal = .{
    .code = .bad_text,
    .message = "this string reaches the end of the line with no closing '\"'",
    .label = "never closes",
    .help = "a string sits on one line, and '\\n' writes a break, " ++
        "or a run of '\\\\' lines spans several",
};

const char_cut: Refusal = .{
    .code = .bad_text,
    .message = "this character reaches the end of the line with no closing quote",
    .label = "never closes",
};

const char_empty: Refusal = .{
    .code = .bad_text,
    .message = "a character literal holds one character, and this one holds none",
    .label = "nothing inside",
};

const char_crowded: Refusal = .{
    .code = .bad_text,
    .message = "a character literal holds one character",
    .label = "more than one",
    .help = "a run of characters is a string, written with '\"'",
};

const unknown_escape: Refusal = .{
    .code = .bad_text,
    .message = "this is not an escape the language knows",
    .label = "unknown escape",
    .help = escapes_help,
};

const bad_byte_escape: Refusal = .{
    .code = .bad_text,
    .message = "'\\x' writes one byte, so it takes two hex digits",
    .label = "not two hex digits",
    .help = "'\\x41' is the byte 65",
};

const bad_codepoint_escape: Refusal = .{
    .code = .bad_text,
    .message = "'\\u' takes a codepoint in braces",
    .label = "not a codepoint in braces",
    .help = "'\\u{1F980}' writes the UTF-8 bytes of that codepoint",
};

const codepoint_too_large: Refusal = .{
    .code = .bad_text,
    .message = "codepoints run to 0x10FFFF, and this one is past it",
    .label = "past the last codepoint",
};

const surrogate: Refusal = .{
    .code = .bad_text,
    .message = "this is half of a surrogate pair, which is not a codepoint",
    .label = "not a codepoint",
    .help = "write the codepoint itself, as in '\\u{1F980}'",
};

const bad_utf8: Refusal = .{
    .code = .bad_text,
    .message = "this character is not valid UTF-8",
    .label = "unreadable",
    .help = "source is UTF-8, and '\\xNN' writes a byte that is not",
};

const testing = std.testing;

test "every base folds, wide values included" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try testing.expectEqual(@as(i128, 0), (try decodeNumber(arena, "0")).int);
    try testing.expectEqual(@as(i128, 1_000_000), (try decodeNumber(arena, "1_000_000")).int);
    try testing.expectEqual(@as(i128, 255), (try decodeNumber(arena, "0xff")).int);
    try testing.expectEqual(@as(i128, 10), (try decodeNumber(arena, "0b1010")).int);
    const past_u64 = try decodeNumber(arena, "18446744073709551616");
    try testing.expectEqual(@as(i128, 1) << 64, past_u64.int);
    try testing.expectEqual(@as(f64, 3.0), (try decodeNumber(arena, "0x1.8p1")).float);
    try testing.expectEqual(@as(f64, 0.25), (try decodeNumber(arena, "2.5e-1")).float);
}

test "every malformed shape is refused, the edges by their width" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    for ([_][]const u8{
        "170141183460469231731687303715884105728", "1e999", "09", "1__0", "0X1", "1$",
    }) |text| {
        const refused = (try decodeNumber(arena, text)).refused;
        try testing.expectEqual(Diagnostic.Code.bad_number, refused.code);
    }
}

fn expectBytes(literal: []const u8, want: []const u8) !void {
    var collected: std.ArrayList(u8) = .empty;
    defer collected.deinit(testing.allocator);

    var reading = bytesOf(literal);
    while (reading.next()) |piece| switch (piece) {
        .bytes => |run| try collected.appendSlice(testing.allocator, run),
        .refused => return error.Refused,
    };
    try testing.expectEqualStrings(want, collected.items);
}

fn expectRefused(literal: []const u8) !void {
    var reading = bytesOf(literal);
    while (reading.next()) |piece| if (piece == .refused) return;
    return error.NotRefused;
}

test "a string is its bytes, raw runs and escapes alike" {
    try expectBytes("\"\"", "");
    try expectBytes("\"hi\"", "hi");
    try expectBytes("\"a\\nb\"", "a\nb");
    try expectBytes("\"\\\\\\\"\\'\"", "\\\"'");
    try expectBytes("\"\\x41\\x7f\"", "A\x7f");
    try expectBytes("\"\\u{1F980}\"", "\u{1F980}");
    try expectBytes("\"h\u{e9}llo\"", "h\u{e9}llo");
}

test "every malformed string is refused, the edges included" {
    // the tokenizer hands over what it read, so an unterminated literal arrives short
    try expectRefused("\"hi");
    try expectRefused("\"hi\\");
    try expectRefused("\"\\q\"");
    try expectRefused("\"\\x4\"");
    try expectRefused("\"\\xzz\"");
    try expectRefused("\"\\u41\"");
    try expectRefused("\"\\u{}\"");
    try expectRefused("\"\\u{110000}\"");
    try expectRefused("\"\\u{D800}\"");
}

test "a '\\\\' line is its bytes, the marker and the line ending dropped" {
    try testing.expectEqualStrings("hi", textLine("\\\\hi"));
    try testing.expectEqualStrings("", textLine("\\\\"));
    try testing.expectEqualStrings("  indented", textLine("\\\\  indented"));
    // raw, so what would be an escape between quotes is the two bytes it spells
    try testing.expectEqualStrings("a\\nb", textLine("\\\\a\\nb"));
    try testing.expectEqualStrings("\"quoted\"", textLine("\\\\\"quoted\""));
    try testing.expectEqualStrings("not // a comment", textLine("\\\\not // a comment"));
    try testing.expectEqualStrings("crlf", textLine("\\\\crlf\r"));
    try testing.expectEqualStrings("kept\r", textLine("\\\\kept\r\r"));
}

test "a character is a number, however it is written" {
    try testing.expectEqual(@as(u32, 'a'), decodeChar("'a'").codepoint);
    try testing.expectEqual(@as(u32, '\n'), decodeChar("'\\n'").codepoint);
    try testing.expectEqual(@as(u32, '\''), decodeChar("'\\''").codepoint);
    try testing.expectEqual(@as(u32, 0x41), decodeChar("'\\x41'").codepoint);
    try testing.expectEqual(@as(u32, 0x1F980), decodeChar("'\\u{1F980}'").codepoint);
    try testing.expectEqual(@as(u32, 0x1F980), decodeChar("'\u{1F980}'").codepoint);
    try testing.expectEqual(@as(u32, 0xE9), decodeChar("'\u{e9}'").codepoint);
}

test "a character literal holds one character, and says so when it does not" {
    try testing.expect(decodeChar("''") == .refused);
    try testing.expect(decodeChar("'") == .refused);
    try testing.expect(decodeChar("'a") == .refused);
    try testing.expect(decodeChar("'ab'") == .refused);
    try testing.expect(decodeChar("'\\q'") == .refused);
    // a lone continuation byte, which no character starts with
    try testing.expect(decodeChar("'\xA9'") == .refused);
}
