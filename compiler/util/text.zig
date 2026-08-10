//! Decodes what a string or a character literal spells, or the refusal to report.

const std = @import("std");
const assert = std.debug.assert;

const number = @import("number.zig");

pub const Refusal = number.Refusal;

const codepoint_max = 0x10FFFF;

pub const Char = union(enum) { codepoint: u32, refused: Refusal };

/// A run of a string's bytes, or the refusal that ends it.
pub const Piece = union(enum) { bytes: []const u8, refused: Refusal };

/// Walks a string literal, so its bytes reach the caller without a buffer between.
pub const Bytes = struct {
    /// The literal as written, quotes included.
    text: []const u8,
    cursor: u32,
    /// Staging for an escape, four being the widest UTF-8 sequence.
    encoded: [4]u8,
    stopped: bool,

    /// The next run, or null at the closing quote. A run lasts until the next call.
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
                        return .{ .bytes = reading.encode(unit) };
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

    /// What an escape stands for, staged inside the iterator.
    fn encode(reading: *Bytes, unit: Unit) []const u8 {
        switch (unit.kind) {
            .byte => {
                assert(unit.value <= std.math.maxInt(u8));
                reading.encoded[0] = @intCast(unit.value);
                return reading.encoded[0..1];
            },
            .codepoint => {
                assert(unit.value <= codepoint_max);
                // the escape refused surrogates, the only other thing encoding rejects
                const width = std.unicode.utf8Encode(
                    @intCast(unit.value),
                    &reading.encoded,
                ) catch unreachable;
                return reading.encoded[0..width];
            },
        }
    }
};

pub fn bytesOf(literal: []const u8) Bytes {
    assert(literal.len > 0);
    assert(literal[0] == '"');
    return .{ .text = literal, .cursor = 1, .encoded = @splat(0), .stopped = false };
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
    return .{ .codepoint = unit.value };
}

/// One character of a literal, and how many of its bytes spell it.
const Unit = struct {
    value: u32,
    width: u32,
    kind: Kind,

    const Kind = enum {
        /// One byte, written as it stands.
        byte,
        /// A codepoint, whose UTF-8 bytes a string holds.
        codepoint,
    };
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
    return .{ .unit = .{ .value = value, .width = 2, .kind = .byte } };
}

/// `\xNN`, one byte in hex.
fn byteEscape(literal: []const u8, at: u32) Read {
    assert(literal[at] == '\\');
    assert(literal[at + 1] == 'x');

    const digits = at + 2;
    if (digits + 2 > literal.len) return .{ .refused = bad_byte_escape };

    const high = std.fmt.charToDigit(literal[digits], 16) catch
        return .{ .refused = bad_byte_escape };
    const low = std.fmt.charToDigit(literal[digits + 1], 16) catch
        return .{ .refused = bad_byte_escape };

    return .{ .unit = .{ .value = @as(u32, high) * 16 + low, .width = 4, .kind = .byte } };
}

/// `\u{1F980}`, a codepoint in braces.
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

    return .{ .unit = .{ .value = value, .width = cursor + 1 - at, .kind = .codepoint } };
}

fn utf8At(literal: []const u8, at: u32) Read {
    assert(at > 0);
    assert(at < literal.len);

    const width = std.unicode.utf8ByteSequenceLength(literal[at]) catch
        return .{ .refused = bad_utf8 };
    if (at + width > literal.len) return .{ .refused = bad_utf8 };

    const value = std.unicode.utf8Decode(literal[at..][0..width]) catch
        return .{ .refused = bad_utf8 };
    return .{ .unit = .{ .value = value, .width = width, .kind = .codepoint } };
}

const escapes_help = "the escapes are '\\n', '\\r', '\\t', '\\\\', '\\'', '\\\"', " ++
    "'\\xNN' for a byte, and '\\u{...}' for a codepoint";

const string_cut: Refusal = .{
    .code = .bad_text,
    .message = "this string reaches the end of the line with no closing '\"'",
    .label = "never closes",
    .help = "a string sits on one line, and '\\n' writes a line break inside it",
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
    while (reading.next()) |piece| {
        if (piece == .refused) return;
    }
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
