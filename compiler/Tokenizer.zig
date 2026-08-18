const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const Source = @import("Source.zig");
const Token = @import("Token.zig");

source: [:0]const u8,
cursor: u32,
/// The last tag returned, never a comment.
previous: Token.Tag,
/// A statement-ending line break, held until the next token rules out a selector.
pending: ?u32,

pub const TokenList = std.MultiArrayList(Token);

/// Comments, set aside for tools. Each runs from its start to the end of the line.
pub const CommentList = std.ArrayList(Token);

const Tokenizer = @This();

pub fn init(source: [:0]const u8) Tokenizer {
    assert(source.len <= Source.bytes_max);

    const bom: u32 = if (std.mem.startsWith(u8, source, "\xEF\xBB\xBF")) 3 else 0;
    return .{ .source = source, .cursor = bom, .previous = .semi, .pending = null };
}

/// Comments are set aside, so the parser never meets one.
pub fn tokenizeAll(
    gpa: Allocator,
    source: [:0]const u8,
    tokens: *TokenList,
    comments: *CommentList,
) Allocator.Error!void {
    assert(tokens.len == 0);
    assert(comments.items.len == 0);

    // about a token per five bytes, a comment per 128. measured on real files
    try tokens.ensureTotalCapacity(gpa, @divFloor(source.len, 5) + 2);
    try comments.ensureTotalCapacity(gpa, @divFloor(source.len, 128) + 2);

    var tokenizer: Tokenizer = .init(source);
    while (true) {
        const token = tokenizer.next();
        if (token.tag.isComment()) {
            try comments.append(gpa, token);
            continue;
        }
        try tokens.append(gpa, token);
        if (token.tag == .eof) break;
    }

    assert(tokens.len > 0);
    assert(tokens.items(.tag)[tokens.len - 1] == .eof);
}

/// The next token, the held `;` first where a line break ended a statement.
pub fn next(tokenizer: *Tokenizer) Token {
    const token = tokenizer.scan();
    if (token.tag.isComment()) return token;
    switch (token.tag) {
        // a line opening with a selector, a range, or another `\\` continues the one above
        .dot, .dot_star, .dot_dot, .string_line => {},
        else => if (tokenizer.insertedSemi(token)) |semi| return semi,
    }

    tokenizer.pending = null;
    tokenizer.previous = token.tag;
    return token;
}

fn insertedSemi(tokenizer: *Tokenizer, token: Token) ?Token {
    const start = tokenizer.pending orelse start: {
        // a file with no trailing newline still ends its last statement
        if (token.tag != .eof) return null;
        if (Token.endsStatement(tokenizer.previous) == false) return null;
        break :start token.start;
    };
    assert(start <= token.start);

    tokenizer.pending = null;
    tokenizer.previous = .semi;
    // back up so the next call rescans this token
    tokenizer.cursor = token.start;
    return .{ .tag = .semi, .start = start };
}

/// One token as it is written, cursor left just past it.
fn scan(tokenizer: *Tokenizer) Token {
    assert(tokenizer.cursor <= tokenizer.source.len);

    const source = tokenizer.source;
    var cursor = tokenizer.cursor;

    while (true) {
        switch (source[cursor]) {
            ' ', '\t', '\r' => cursor += 1,
            '\n' => {
                const ends = Token.endsStatement(tokenizer.previous);
                if (ends and tokenizer.pending == null) tokenizer.pending = cursor;
                cursor += 1;
            },
            else => break,
        }
    }

    const start = cursor;
    const tag: Token.Tag = state: switch (State.start) {
        .start => switch (source[cursor]) {
            0 => {
                if (cursor != source.len) continue :state .invalid;
                break :state .eof;
            },
            'a'...'z', 'A'...'Z', '_' => continue :state .ident,
            '0'...'9' => continue :state .number,
            // `//` opens a comment, so `/` cannot go through the table below
            '/' => continue :state .slash,
            '"' => continue :state .string,
            '\'' => continue :state .char,
            // `\\` opens a line of a multi-line string, and one `\` is stray bytes
            '\\' => continue :state if (source[cursor + 1] == '\\') .string_line else .invalid,
            // `@` opens a builtin only when a name follows, and is stray bytes otherwise
            '@' => continue :state if (is_ident[source[cursor + 1]]) .builtin else .invalid,
            else => {
                for (Token.punctuation[source[cursor]].candidates()) |candidate| {
                    const text = candidate.lexeme().?;
                    if (std.mem.startsWith(u8, source[cursor..], text)) {
                        cursor += @intCast(text.len);
                        break :state candidate;
                    }
                }
                continue :state .invalid;
            },
        },

        .ident => {
            cursor = identEnd(source, cursor);
            assert(cursor > start);
            break :state Token.keywordOrIdent(source[start..cursor]);
        },

        .number => {
            cursor = numberEnd(source, cursor);
            assert(cursor > start);
            break :state .number;
        },

        .string => {
            cursor = quotedEnd(source, cursor, '"');
            assert(cursor > start);
            break :state .string;
        },

        .char => {
            cursor = quotedEnd(source, cursor, '\'');
            assert(cursor > start);
            break :state .char;
        },

        // the line is raw, so nothing inside it opens a comment or an escape
        .string_line => {
            assert(source[cursor] == '\\');
            assert(source[cursor + 1] == '\\');
            cursor = endOfLine(source, cursor);
            assert(cursor >= start + 2);
            break :state .string_line;
        },

        .builtin => {
            assert(source[cursor] == '@');
            cursor = identEnd(source, cursor + 1);
            break :state .builtin;
        },

        .slash => {
            assert(source[cursor] == '/');
            cursor += 1;
            if (source[cursor] == '/') continue :state .comment_start;
            if (source[cursor] == '=') {
                cursor += 1;
                break :state .slash_eq;
            }
            break :state .slash;
        },

        .comment_start => {
            assert(source[cursor] == '/');
            cursor += 1;
            // `//!` the file, `///` the declaration below, `////` neither
            const kind: Token.Tag = switch (source[cursor]) {
                '!' => .file_doc_comment,
                '/' => if (source[cursor + 1] == '/') .comment else .doc_comment,
                else => .comment,
            };
            cursor = endOfLine(source, cursor);
            assert(cursor >= start + 2);
            break :state kind;
        },

        .invalid => {
            @branchHint(.cold);
            cursor += 1;
            if (cursor == source.len) break :state .invalid;
            if (is_token_start[source[cursor]]) break :state .invalid;
            continue :state .invalid;
        },
    };

    assert(cursor <= source.len);
    assert(start <= cursor);
    if (cursor == start) assert(tag == .eof);

    tokenizer.cursor = cursor;
    return .{ .tag = tag, .start = start };
}

/// Byte just past a token. Rescans, tokens don't store lengths.
pub fn tokenEnd(source: [:0]const u8, tag: Token.Tag, start: u32) u32 {
    assert(start <= source.len);

    const fixed = Token.lexeme_len[@intFromEnum(tag)];
    if (fixed > 0) return start + fixed;

    switch (tag) {
        .eof => return start,
        .ident => return identEnd(source, start),
        // past the `@`, which the name follows
        .builtin => return identEnd(source, start + 1),
        .number => return numberEnd(source, start),
        .string => return quotedEnd(source, start, '"'),
        .string_line => return endOfLine(source, start),
        .char => return quotedEnd(source, start, '\''),
        .comment, .doc_comment, .file_doc_comment => return endOfLine(source, start),
        .invalid => {
            assert(start < source.len);
            var cursor = start + 1;
            while (cursor < source.len and is_token_start[source[cursor]] == false) cursor += 1;
            return cursor;
        },
        // every remaining tag spells fixed text, so the table answered above
        else => unreachable,
    }
}

fn identEnd(source: [:0]const u8, start: u32) u32 {
    assert(is_ident[source[start]]);
    var cursor = start;
    while (is_ident[source[cursor]]) cursor += 1;
    return cursor;
}

/// Past the closing quote, or at the line's end where the literal never closed.
fn quotedEnd(source: [:0]const u8, start: u32, quote: u8) u32 {
    assert(start < source.len);
    assert(source[start] == quote);

    const end = end: {
        var cursor = start + 1;
        while (cursor < source.len) {
            switch (source[cursor]) {
                '\n' => break :end cursor,
                '\\' => {
                    if (cursor + 1 == source.len) break;
                    // the escape takes the byte after it, so a quote there does not close
                    if (source[cursor + 1] == '\n') break :end cursor + 1;
                    cursor += 2;
                },
                else => |byte| {
                    cursor += 1;
                    if (byte == quote) break :end cursor;
                },
            }
        }
        break :end @as(u32, @intCast(source.len));
    };

    assert(end > start);
    assert(end <= source.len);
    return end;
}

fn numberEnd(source: [:0]const u8, start: u32) u32 {
    assert(source[start] >= '0');
    assert(source[start] <= '9');

    var cursor = start;
    while (true) {
        while (is_ident[source[cursor]]) cursor += 1;
        switch (source[cursor]) {
            // a fraction continues only into a digit, so `x.f` stays a selector
            '.' => switch (source[cursor + 1]) {
                '0'...'9' => cursor += 1,
                else => return cursor,
            },
            // a sign continues only an exponent, so `1e5-2` stays a subtraction
            '+', '-' => switch (source[cursor - 1]) {
                'e', 'E', 'p', 'P' => cursor += 1,
                else => return cursor,
            },
            else => return cursor,
        }
    }
}

const State = enum {
    start,
    ident,
    number,
    string,
    string_line,
    char,
    builtin,
    slash,
    comment_start,
    invalid,
};

/// Bounded by `Source.bytes_max`, which keeps every offset a `u32`.
pub fn endOfLine(source: [:0]const u8, from: u32) u32 {
    assert(from <= source.len);
    const newline = std.mem.indexOfScalarPos(u8, source, from, '\n') orelse source.len;
    assert(newline >= from);
    return @intCast(newline);
}

const is_ident = classOf("_0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");

/// Where a run of invalid bytes stops. Derived, so a new operator joins it.
const is_token_start = build: {
    var table = classOf(" \t\r\n_0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");
    // a quote or a `\` opens a literal and `@` opens a builtin, which no lexeme names
    table['"'] = true;
    table['\''] = true;
    table['\\'] = true;
    table['@'] = true;
    for (Token.punctuation, 0..) |group, byte| {
        if (group.count > 0) table[byte] = true;
    }
    break :build table;
};

fn classOf(comptime members: []const u8) [256]bool {
    comptime assert(members.len > 0);
    var table: [256]bool = @splat(false);
    for (members) |byte| table[byte] = true;
    return table;
}
