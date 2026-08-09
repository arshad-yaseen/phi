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

/// Set aside for tools.
pub const Comment = struct {
    kind: Kind,
    /// No end is stored. The text runs to the end of the line.
    start: u32,

    pub const Kind = enum { plain, doc, file };
};

pub const CommentList = std.ArrayList(Comment);

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

    // one token per five bytes, one comment per hundred and twenty-eight
    try tokens.ensureTotalCapacity(gpa, @divFloor(source.len, 5) + 2);
    try comments.ensureTotalCapacity(gpa, @divFloor(source.len, 128) + 2);

    var tokenizer: Tokenizer = .init(source);
    while (true) {
        const token = tokenizer.next();
        if (commentKind(token.tag)) |kind| {
            try comments.append(gpa, .{ .kind = kind, .start = token.start });
            continue;
        }
        try tokens.append(gpa, token);
        if (token.tag == .eof) break;
    }

    assert(tokens.len > 0);
    assert(tokens.items(.tag)[tokens.len - 1] == .eof);
}

fn commentKind(tag: Token.Tag) ?Comment.Kind {
    return switch (tag) {
        .comment => .plain,
        .doc_comment => .doc,
        .file_doc_comment => .file,
        else => null,
    };
}

/// The next token, the held `;` first where a line break ended a statement.
pub fn next(tokenizer: *Tokenizer) Token {
    const token = tokenizer.scan();
    switch (token.tag) {
        .comment, .doc_comment, .file_doc_comment => return token,
        // a line that opens with a selector or a range continues the one above
        .dot, .dot_star, .dot_dot => {},
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
    // the token that follows is scanned again on the next call
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
            if (source[cursor] == '!') continue :state .file_doc_comment;
            if (source[cursor] == '/') {
                if (source[cursor + 1] == '/') continue :state .line_comment;
                continue :state .doc_comment;
            }
            continue :state .line_comment;
        },

        .line_comment => {
            cursor = endOfLine(source, cursor);
            break :state .comment;
        },

        .doc_comment => {
            cursor = endOfLine(source, cursor);
            assert(cursor >= start + 3);
            break :state .doc_comment;
        },

        .file_doc_comment => {
            cursor = endOfLine(source, cursor);
            assert(cursor >= start + 3);
            break :state .file_doc_comment;
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

/// The byte just past a token, rescanned, so none stores a length.
pub fn tokenEnd(source: [:0]const u8, tag: Token.Tag, start: u32) u32 {
    assert(start <= source.len);

    const fixed = Token.lexeme_len[@intFromEnum(tag)];
    if (fixed > 0) return start + fixed;

    switch (tag) {
        .eof => return start,
        .ident => return identEnd(source, start),
        .number => return numberEnd(source, start),
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

/// Where the scan is inside one token.
const State = enum {
    start,
    ident,
    number,
    slash,
    comment_start,
    line_comment,
    doc_comment,
    file_doc_comment,
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
