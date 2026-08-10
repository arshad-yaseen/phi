const std = @import("std");
const assert = std.debug.assert;

tag: Tag,
/// The end is rescanned by `Tokenizer.tokenEnd`, never stored.
start: u32,

pub const Tag = enum(u8) {
    /// Bytes that cannot begin a token.
    invalid,
    eof,

    ident,
    number,
    string,
    char,
    /// `@name`, an operation the compiler performs itself.
    builtin,

    comment,
    /// Belongs to the declaration below.
    doc_comment,
    file_doc_comment,

    kw_and,
    kw_break,
    kw_continue,
    kw_defer,
    kw_else,
    kw_fn,
    kw_if,
    kw_import,
    kw_in,
    kw_is,
    kw_let,
    kw_loop,
    kw_match,
    kw_not,
    kw_or,
    kw_pub,
    kw_return,
    kw_type,
    kw_var,

    l_paren,
    r_paren,
    l_brace,
    r_brace,
    l_bracket,
    r_bracket,
    comma,
    dot,
    /// One token, so a line ending in `p.*` ends its statement.
    dot_star,
    /// `a..b`, the ends of a range.
    dot_dot,
    colon,
    /// Written, or inserted at a line break.
    semi,
    pipe,

    eq,
    eq_eq,
    /// `=>`, between a match arm's label and its body.
    eq_arrow,
    bang_eq,
    lt,
    lt_eq,
    gt,
    gt_eq,
    plus,
    minus,
    star,
    slash,
    percent,
    ampersand,
    caret,
    tilde,
    lt_lt,
    gt_gt,

    plus_eq,
    minus_eq,
    star_eq,
    slash_eq,
    percent_eq,
    ampersand_eq,
    pipe_eq,
    caret_eq,
    lt_lt_eq,
    gt_gt_eq,

    /// Fixed text, or null when the text is the source itself.
    pub fn lexeme(tag: Tag) ?[]const u8 {
        return switch (tag) {
            .invalid, .eof => null,
            .ident, .number, .string, .char, .builtin => null,
            .comment, .doc_comment, .file_doc_comment => null,

            .kw_and => "and",
            .kw_break => "break",
            .kw_continue => "continue",
            .kw_defer => "defer",
            .kw_else => "else",
            .kw_fn => "fn",
            .kw_if => "if",
            .kw_import => "import",
            .kw_in => "in",
            .kw_is => "is",
            .kw_let => "let",
            .kw_loop => "loop",
            .kw_match => "match",
            .kw_not => "not",
            .kw_or => "or",
            .kw_pub => "pub",
            .kw_return => "return",
            .kw_type => "type",
            .kw_var => "var",

            .l_paren => "(",
            .r_paren => ")",
            .l_brace => "{",
            .r_brace => "}",
            .l_bracket => "[",
            .r_bracket => "]",
            .comma => ",",
            .dot => ".",
            .dot_star => ".*",
            .dot_dot => "..",
            .colon => ":",
            .semi => ";",
            .pipe => "|",

            .eq => "=",
            .eq_eq => "==",
            .eq_arrow => "=>",
            .bang_eq => "!=",
            .lt => "<",
            .lt_eq => "<=",
            .gt => ">",
            .gt_eq => ">=",
            .plus => "+",
            .minus => "-",
            .star => "*",
            .slash => "/",
            .percent => "%",
            .ampersand => "&",
            .caret => "^",
            .tilde => "~",
            .lt_lt => "<<",
            .gt_gt => ">>",

            .plus_eq => "+=",
            .minus_eq => "-=",
            .star_eq => "*=",
            .slash_eq => "/=",
            .percent_eq => "%=",
            .ampersand_eq => "&=",
            .pipe_eq => "|=",
            .caret_eq => "^=",
            .lt_lt_eq => "<<=",
            .gt_gt_eq => ">>=",
        };
    }

    /// How a message names this tag.
    pub fn symbol(tag: Tag) []const u8 {
        const text = symbols[@intFromEnum(tag)];
        assert(text.len > 0);
        return text;
    }

    fn isKeyword(tag: Tag) bool {
        return std.mem.startsWith(u8, @tagName(tag), "kw_");
    }
};

pub const Index = enum(u32) {
    first = 0,
    _,

    pub fn after(index: Index, count: u32) Index {
        assert(@intFromEnum(index) <= std.math.maxInt(u32) - count);
        return @enumFromInt(@intFromEnum(index) + count);
    }

    pub fn before(index: Index, count: u32) Index {
        assert(count > 0);
        assert(@intFromEnum(index) >= count);
        return @enumFromInt(@intFromEnum(index) - count);
    }

    pub fn from(raw: usize) Index {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(@as(u32, @intCast(raw)));
    }

    pub fn int(index: Index) u32 {
        return @intFromEnum(index);
    }
};

pub const tag_count = @typeInfo(Tag).@"enum".fields.len;

/// The tags whose spelling begins with one byte, longest first.
pub const Punctuation = struct {
    tags: [max]Tag,
    count: u8,

    /// `<`, `<=`, `<<`, and `<<=` are the largest group.
    pub const max = 4;

    pub fn candidates(group: *const Punctuation) []const Tag {
        assert(group.count <= max);
        return group.tags[0..group.count];
    }
};

const Token = @This();

comptime {
    assert(@sizeOf(Tag) == 1);
    assert(@sizeOf(Token) == 8);
    assert(@sizeOf(Index) == 4);
}

/// Whether a line break after this tag ends a statement.
pub fn endsStatement(tag: Tag) bool {
    return switch (tag) {
        .ident, .number, .string, .char, .builtin, .invalid => true,
        .r_paren, .r_brace, .r_bracket => true,
        .dot_star => true,
        .kw_return, .kw_break, .kw_continue => true,
        else => false,
    };
}

pub fn keywordOrIdent(bytes: []const u8) Tag {
    assert(bytes.len > 0);
    return keywords.get(bytes) orelse .ident;
}

/// Derived from `lexeme`, so the table cannot drift from the tags.
const keywords = build: {
    @setEvalBranchQuota(8000);
    const tags = std.enums.values(Tag);
    var entries: [tags.len]struct { []const u8, Tag } = undefined;
    var count = 0;
    for (tags) |tag| {
        if (tag.isKeyword() == false) continue;
        entries[count] = .{ tag.lexeme().?, tag };
        count += 1;
    }
    assert(count > 0);
    break :build std.StaticStringMap(Tag).initComptime(entries[0..count].*);
};

/// Derived, longest first, which is what makes `<<=` win over `<<`.
pub const punctuation: [256]Punctuation = build: {
    @setEvalBranchQuota(8000);
    var table: [256]Punctuation = @splat(.{ .tags = @splat(.invalid), .count = 0 });

    var longest = 0;
    for (std.enums.values(Tag)) |tag| {
        if (tag.isKeyword()) continue;
        const text = tag.lexeme() orelse continue;
        longest = @max(longest, text.len);
    }
    assert(longest == 3);

    var length = longest;
    while (length > 0) : (length -= 1) {
        for (std.enums.values(Tag)) |tag| {
            if (tag.isKeyword()) continue;
            const text = tag.lexeme() orelse continue;
            if (text.len != length) continue;

            const group = &table[text[0]];
            assert(group.count < Punctuation.max);
            group.tags[group.count] = tag;
            group.count += 1;
        }
    }
    break :build table;
};

/// Each fixed spelling's length, zero where the text is the source itself.
pub const lexeme_len: [tag_count]u8 = blk: {
    @setEvalBranchQuota(8000);
    var table: [tag_count]u8 = @splat(0);
    for (std.enums.values(Tag)) |tag| {
        if (tag.lexeme()) |text| table[@intFromEnum(tag)] = text.len;
    }
    break :blk table;
};

const symbols: [tag_count][]const u8 = blk: {
    @setEvalBranchQuota(8000);
    var table: [tag_count][]const u8 = @splat("");
    for (std.enums.values(Tag)) |tag| {
        table[@intFromEnum(tag)] = switch (tag) {
            .invalid => "invalid bytes",
            .eof => "end of file",
            .ident => "an identifier",
            .number => "a number",
            .string => "a string",
            .char => "a character",
            .builtin => "a builtin",
            .comment => "a comment",
            .doc_comment => "a doc comment",
            .file_doc_comment => "a file doc comment",
            .semi => "the end of the line",
            else => quoted: {
                const text = tag.lexeme() orelse
                    @compileError("tag needs a phrase or a lexeme: " ++ @tagName(tag));
                break :quoted "'" ++ text ++ "'";
            },
        };
        assert(table[@intFromEnum(tag)].len > 0);
    }
    break :blk table;
};
