const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Diagnostic = @import("Diagnostic.zig");
const Token = @import("Token.zig");
const Source = @import("Source.zig");
const Tokenizer = @import("Tokenizer.zig");

const Node = AST.Node;

const Parse = @This();

pub const depth_max = 128;
pub const type_params_max = 16;
/// The reporting budget. Reaching it mutes reports and never stops parsing.
const errors_max = 64;

gpa: Allocator,
/// Backs `errors` and its strings.
arena: std.heap.ArenaAllocator,
source: [:0]const u8,
tokens: Tokenizer.TokenList.Slice,
/// The column the cursor reads on nearly every step.
tags: []const Token.Tag,
/// The `.eof` the cursor never passes.
eof_index: Token.Index,
/// Only ever moves forward.
token_index: Token.Index,
nodes: std.MultiArrayList(AST.Node),
extra: std.ArrayList(u32),
scratch: std.ArrayList(Node.Index),
errors: std.ArrayList(Diagnostic),
depth: u32,
/// In an `if` or `loop` header, where a block after `or` belongs to the header.
in_condition: bool,
reported_too_deep: bool,

pub fn run(gpa: Allocator, source: [:0]const u8) Allocator.Error!AST {
    assert(source.len <= Source.bytes_max);

    var tokens: Tokenizer.TokenList = .empty;
    errdefer tokens.deinit(gpa);

    var comments: Tokenizer.CommentList = .empty;
    errdefer comments.deinit(gpa);

    try Tokenizer.tokenizeAll(gpa, source, &tokens, &comments);
    assert(tokens.len > 0);

    var parse: Parse = .{
        .gpa = gpa,
        .arena = .init(gpa),
        .source = source,
        .tokens = tokens.slice(),
        .tags = tokens.items(.tag),
        .eof_index = .from(tokens.len - 1),
        .token_index = .first,
        .nodes = .empty,
        .extra = .empty,
        .scratch = .empty,
        .errors = .empty,
        .depth = 0,
        .in_condition = false,
        .reported_too_deep = false,
    };
    defer parse.scratch.deinit(gpa);

    errdefer {
        parse.nodes.deinit(gpa);
        parse.extra.deinit(gpa);
        parse.arena.deinit();
    }

    // a node per eight bytes, an extra word per sixteen, a scratch slot per sixty-four
    try parse.nodes.ensureTotalCapacity(gpa, @divFloor(source.len, 8) + 8);
    try parse.extra.ensureTotalCapacity(gpa, @divFloor(source.len, 16) + 8);
    try parse.scratch.ensureTotalCapacity(gpa, @divFloor(source.len, 64) + 8);

    try parse.parseRoot();
    assert(parse.nodes.len > 0);
    assert(parse.scratch.items.len == 0);
    assert(parse.depth == 0);

    const extra = try parse.extra.toOwnedSlice(gpa);
    errdefer gpa.free(extra);

    const errors = try parse.errors.toOwnedSlice(parse.arena.allocator());

    return .{
        .source = source,
        .tokens = tokens.toOwnedSlice(),
        .comments = try comments.toOwnedSlice(gpa),
        .nodes = parse.nodes.toOwnedSlice(),
        .extra = extra,
        .errors = errors,
        .error_text = parse.arena.state,
    };
}

// the cursor

/// The cursor never passes the `.eof`, so the read is always in bounds.
fn current(self: *const Parse) Token.Tag {
    assert(self.token_index.int() <= self.eof_index.int());
    return self.tags[self.token_index.int()];
}

/// The tag `ahead` tokens past the cursor, `.eof` past the end.
fn peek(self: *const Parse, ahead: u32) Token.Tag {
    assert(ahead > 0);
    const index = self.token_index.int() + ahead;
    if (index < self.tags.len) return self.tags[index];
    return .eof;
}

fn at(self: *const Parse, expected: Token.Tag) bool {
    assert(self.token_index.int() <= self.eof_index.int());
    return self.current() == expected;
}

fn eof(self: *const Parse) bool {
    assert(self.eof_index.int() < self.tags.len);
    return self.token_index.int() >= self.eof_index.int();
}

/// Stops at the `.eof`, so the cursor always names a token.
fn nextToken(self: *Parse) Token.Index {
    assert(self.token_index.int() <= self.eof_index.int());

    const consumed = self.token_index;
    if (self.eof()) return consumed;

    self.token_index = self.token_index.after(1);
    assert(self.token_index.int() <= self.eof_index.int());
    return consumed;
}

fn eatToken(self: *Parse, expected: Token.Tag) ?Token.Index {
    assert(expected != .eof);
    return if (self.at(expected)) self.nextToken() else null;
}

fn ensureProgress(self: *Parse, before: Token.Index) void {
    assert(self.token_index.int() >= before.int());

    if (self.token_index == before) _ = self.nextToken();

    if (self.eof() == false) assert(self.token_index.int() > before.int());
}

// nesting

/// One level deeper, or false at the limit. Every true `enter` pairs with a `leave`.
fn enter(self: *Parse) bool {
    assert(self.depth <= depth_max);
    if (self.depth == depth_max) return false;
    self.depth += 1;
    return true;
}

fn leave(self: *Parse) void {
    assert(self.depth > 0);
    self.depth -= 1;
}

// spans

fn spanOf(self: *const Parse, index: Token.Index) Diagnostic.Span {
    const start = self.tokens.items(.start)[index.int()];
    const end = Tokenizer.tokenEnd(self.source, self.tags[index.int()], start);
    return .{ .start = start, .end = @min(end, @as(u32, @intCast(self.source.len))) };
}

fn here(self: *const Parse) Diagnostic.Span {
    assert(self.token_index.int() <= self.eof_index.int());
    return self.spanOf(self.token_index);
}

/// From `from` to the last token consumed.
fn spanSince(self: *const Parse, from: Token.Index) Diagnostic.Span {
    assert(from.int() <= self.token_index.int());
    const last = if (self.token_index.int() > from.int()) self.token_index.before(1) else from;
    return .{ .start = self.spanOf(from).start, .end = self.spanOf(last).end };
}

// diagnostics

fn fmt(self: *Parse, comptime template: []const u8, args: anytype) Allocator.Error![]const u8 {
    comptime assert(template.len > 0);
    return std.fmt.allocPrint(self.arena.allocator(), template, args);
}

fn err(self: *Parse, diagnostic: Diagnostic) Allocator.Error!void {
    @branchHint(.cold);
    assert(diagnostic.message.len > 0);
    assert(diagnostic.span.start <= diagnostic.span.end);

    // unwinding recovery re-asks, so an identical report at this spot is an echo
    var index = self.errors.items.len;
    while (index > 0) {
        index -= 1;
        const previous = self.errors.items[index];
        if (previous.span.start != diagnostic.span.start) break;
        if (previous.code != diagnostic.code) continue;
        if (std.mem.eql(u8, previous.message, diagnostic.message)) return;
    }

    if (self.errors.items.len == errors_max) return;
    try self.errors.append(self.arena.allocator(), diagnostic);
}

fn errExpected(
    self: *Parse,
    code: Diagnostic.Code,
    what: []const u8,
    help: ?[]const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(what.len > 0);
    try self.err(.{
        .code = code,
        .span = self.here(),
        .message = try self.fmt("expected {s}, found {s}", .{ what, self.current().symbol() }),
        .label = try self.fmt("expected {s}", .{what}),
        .help = help,
    });
}

fn expectToken(self: *Parse, expected: Token.Tag) Allocator.Error!void {
    assert(expected != .eof);
    if (self.eatToken(expected) == null) {
        try self.errExpected(.expected_token, expected.symbol(), null);
    }
}

fn expectClosing(self: *Parse, closer: Token.Tag, opener: ?Token.Index) Allocator.Error!void {
    assert(closer.lexeme() != null);
    if (self.eatToken(closer) != null) return;
    const open = opener orelse return self.errExpected(.expected_token, closer.symbol(), null);
    const opened = self.tags[open.int()].symbol();
    const found = self.current().symbol();

    try self.err(.{
        .code = .expected_token,
        .span = self.here(),
        .message = try self.fmt("expected {s}, found {s}", .{ closer.symbol(), found }),
        .label = try self.fmt("expected {s}", .{closer.symbol()}),
        .notes = try self.arena.allocator().dupe(Diagnostic.Note, &.{.{
            .message = try self.fmt("to close the {s} opened here", .{opened}),
            .span = self.spanOf(open),
        }}),
    });
}

fn errChainedComparison(self: *Parse) Allocator.Error!void {
    @branchHint(.cold);
    try self.err(.{
        .code = .chained_comparison,
        .span = self.here(),
        .message = "comparisons cannot be chained",
        .label = "a second comparison",
        .help = "write it as two comparisons joined with 'and'",
    });
}

/// The first overflow reports, and parsing carries on with holes.
fn tooDeep(self: *Parse) Allocator.Error!Node.Index {
    @branchHint(.cold);
    if (self.reported_too_deep == false) {
        self.reported_too_deep = true;
        try self.err(.{
            .code = .nesting_too_deep,
            .span = self.here(),
            .message = try self.fmt("this nests more than {d} levels deep", .{depth_max}),
            .label = "too deep",
            .help = "split it into shallower pieces",
        });
    }
    return self.hole();
}

// recovery

/// Over the rest of an item, so one mistake reports once.
fn skipToTerminator(self: *Parse, closer: Token.Tag) void {
    assert(self.token_index.int() <= self.eof_index.int());

    while (self.eof() == false and self.at(closer) == false and
        self.at(.semi) == false and self.at(.comma) == false and self.at(.r_brace) == false)
    {
        self.token_index = self.token_index.after(1);
    }
    _ = self.eatTerminators();

    assert(self.token_index.int() <= self.eof_index.int());
}

/// What stood between two items. Only a bare line break leaves doubt.
const Terminator = enum { none, line, comma };

/// An end of line, a ',' and a ';' all end an item, and a run of them ends one.
fn eatTerminators(self: *Parse) Terminator {
    var found: Terminator = .none;
    while (self.at(.semi) or self.at(.comma)) {
        if (self.at(.comma)) found = .comma else if (found == .none) found = .line;
        self.token_index = self.token_index.after(1);
    }
    return found;
}

/// Every item ends the same way, and a bracket ends the last one for free.
fn expectTerminator(self: *Parse, closer: Token.Tag) Allocator.Error!void {
    if (self.eatTerminators() != .none) return;
    switch (self.current()) {
        // a bracket or the file itself also ends an item
        .r_paren, .r_bracket, .r_brace, .eof => return,
        else => {},
    }
    try self.err(.{
        .code = .expected_token,
        .span = self.here(),
        .message = try self.fmt("expected ',' or the end of the line, found {s}", .{
            self.current().symbol(),
        }),
        .label = "unexpected here",
        .help = "one per line, or a ',' between them",
    });
    self.skipToTerminator(closer);
}

/// A line opening with one of these may continue the line above. `.` is already joined.
const continues_line = TokenSet.initMany(&.{
    .minus,     .ampersand,
    .tilde,     .l_paren,
    .l_bracket,
});

fn errAmbiguousLine(self: *Parse) Allocator.Error!void {
    @branchHint(.cold);
    try self.err(.{
        .code = .ambiguous_line,
        .span = self.here(),
        .message = try self.fmt("this line opens with {s}, which may continue the line above", .{
            self.current().symbol(),
        }),
        .label = "unclear what this belongs to",
        .help = "move it up to continue that line, or write ',' before it to start a new one",
    });
}

// nodes and payloads

fn addNode(self: *Parse, node: Node) Allocator.Error!Node.Index {
    assert(node.main_token.int() < self.tags.len);
    if (self.nodes.len >= std.math.maxInt(u32)) return error.OutOfMemory;

    const index: Node.Index = .from(self.nodes.len);
    try self.nodes.append(self.gpa, node);

    assert(self.nodes.len == index.int() + 1);
    return index;
}

fn addLeaf(self: *Parse, node_tag: Node.Tag) Allocator.Error!Node.Index {
    assert(self.eof() == false or self.current() == .eof);
    const token = self.nextToken();
    return self.addNode(.{ .tag = node_tag, .main_token = token, .data = .{ .none = {} } });
}

fn addUnary(
    self: *Parse,
    node_tag: Node.Tag,
    main_token: Token.Index,
    operand: Node.Index,
) Allocator.Error!Node.Index {
    assert(operand.int() < self.nodes.len);
    return self.addNode(.{
        .tag = node_tag,
        .main_token = main_token,
        .data = .{ .node = operand },
    });
}

fn addPair(
    self: *Parse,
    node_tag: Node.Tag,
    main_token: Token.Index,
    lhs: Node.Index,
    rhs: Node.Index,
) Allocator.Error!Node.Index {
    assert(lhs.int() < self.nodes.len);
    assert(rhs.int() < self.nodes.len);
    return self.addNode(.{
        .tag = node_tag,
        .main_token = main_token,
        .data = .{ .node_and_node = .{ lhs, rhs } },
    });
}

fn hole(self: *Parse) Allocator.Error!Node.Index {
    @branchHint(.cold);
    assert(self.token_index.int() <= self.eof_index.int());
    return self.addNode(.{ .tag = .err, .main_token = self.token_index, .data = .{ .none = {} } });
}

/// A hole over a token nothing can use, stepping past it so the caller moves.
fn skip(self: *Parse) Allocator.Error!Node.Index {
    @branchHint(.cold);

    const before = self.token_index;
    const node = try self.hole();
    _ = self.nextToken();

    if (self.eof() == false) assert(self.token_index.int() > before.int());
    return node;
}

/// Bounded by the appends below, which keep the length inside a `u32`.
fn extraStart(self: *const Parse) AST.ExtraIndex {
    assert(self.extra.items.len < std.math.maxInt(u32));
    return .from(self.extra.items.len);
}

fn extraWord(self: *Parse, word: u32) Allocator.Error!void {
    if (self.extra.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;

    const before = self.extra.items.len;
    try self.extra.append(self.gpa, word);

    assert(self.extra.items.len == before + 1);
    assert(self.extra.items[before] == word);
}

fn extraNode(self: *Parse, node: Node.Index) Allocator.Error!void {
    assert(node.int() < self.nodes.len);
    try self.extraWord(@intFromEnum(node));
}

fn extraOpt(self: *Parse, node: Node.OptionalIndex) Allocator.Error!void {
    if (node.unwrap()) |present| assert(present.int() < self.nodes.len);
    try self.extraWord(@intFromEnum(node));
}

fn extraList(self: *Parse, items: []const Node.Index) Allocator.Error!void {
    // one item per node at most
    assert(items.len <= self.nodes.len);
    try self.extraWord(@intCast(items.len));

    if (self.extra.items.len + items.len > std.math.maxInt(u32)) return error.OutOfMemory;
    try self.extra.ensureUnusedCapacity(self.gpa, items.len);
    self.extra.appendSliceAssumeCapacity(@ptrCast(items));
}

const TokenSet = std.EnumSet(Token.Tag);

const starts_expr = TokenSet.initMany(&.{
    .ident,     .number,
    .string,    .char,
    .l_paren,   .dot,
    .l_bracket, .minus,
    .kw_not,    .tilde,
    .ampersand, .invalid,
    .kw_if,     .kw_loop,
    .kw_match,  .kw_return,
    .kw_break,  .kw_continue,
    .builtin,
});

const starts_stmt = starts_expr.unionWith(TokenSet.initMany(&.{
    .kw_let, .kw_var, .kw_defer, .kw_else,
}));

const starts_member = TokenSet.initMany(&.{ .ident, .kw_fn, .kw_pub });

const starts_type = TokenSet.initMany(&.{ .ident, .star, .l_bracket });

/// Whatever opens a type argument or an index, which a bracket may hold.
const starts_bracket_item = starts_expr.unionWith(TokenSet.initMany(&.{ .star, .l_bracket }));

const starts_name = TokenSet.initOne(.ident);

/// A label opens like a type, and `else` labels the rest.
const starts_arm = TokenSet.initMany(&.{ .ident, .star, .l_bracket, .kw_else });

const starts_decl = TokenSet.initMany(&.{
    .kw_pub, .kw_import, .kw_type,
    .kw_fn,  .kw_let,    .kw_var,
});

const ends_list = starts_decl.unionWith(TokenSet.initMany(&.{ .l_brace, .r_brace, .semi }));

/// Every list, a file, a block, a struct body, and everything bracketed.
const List = struct {
    /// Each element lands in `scratch`.
    item: *const fn (*Parse) Allocator.Error!Node.Index,
    starts: TokenSet,
    /// `.eof` for the file, which no bracket closes.
    closer: Token.Tag,
    /// Null when the opening bracket was itself missing.
    opener: ?Token.Index,
    code: Diagnostic.Code,
    /// Named in "expected _, found ...".
    expected: []const u8,
    help: ?[]const u8 = null,
    /// What means this list was never closed. Nothing does, for a file.
    bails: TokenSet = ends_list,
};

fn skipItem(self: *Parse, closer: Token.Tag) Allocator.Error!Node.Index {
    @branchHint(.cold);
    const node = try self.hole();
    while (self.eof() == false) {
        if (self.at(.comma)) break;
        if (self.at(closer)) break;
        if (ends_list.contains(self.current())) break;
        self.token_index = self.token_index.after(1);
    }
    return node;
}

fn parseList(self: *Parse, list: List) Allocator.Error!void {
    assert(list.expected.len > 0);

    var item_end = self.token_index;
    var line_break_only = false;
    // a run of junk between two good items is one mistake, so it reports once
    var in_junk_run = false;
    while (self.at(list.closer) == false and self.eof() == false) {
        const before = self.token_index;

        if (list.starts.contains(self.current())) {
            in_junk_run = false;
            if (line_break_only and continues_line.contains(self.current())) {
                try self.errAmbiguousLine();
            }
            try self.scratch.append(self.gpa, try list.item(self));
        } else {
            if (list.bails.contains(self.current())) break;
            if (in_junk_run == false) {
                try self.errExpected(list.code, list.expected, list.help);
            }
            in_junk_run = true;
            try self.scratch.append(self.gpa, try self.skipItem(list.closer));
        }

        self.ensureProgress(before);
        item_end = self.token_index;
        const terminator = self.eatTerminators();
        line_break_only = terminator == .line;
        if (terminator == .none) {
            if (self.at(list.closer) or self.eof()) break;
            try self.expectTerminator(list.closer);
        }
    }
    if (list.closer == .eof) return;

    // a list that never closed ran out at the end of its last line
    if (self.at(list.closer) == false and self.tags[item_end.int()] == .semi) {
        self.token_index = item_end;
    }
    try self.expectClosing(list.closer, list.opener);
}

// declarations

fn parseRoot(self: *Parse) Allocator.Error!void {
    assert(self.nodes.len == 0);
    const root = try self.addNode(.{ .tag = .root, .main_token = .first, .data = .{ .none = {} } });
    assert(root == .root);

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseDecl,
        .starts = starts_decl,
        .closer = .eof,
        .opener = null,
        .code = .expected_declaration,
        .expected = "a declaration",
        .help = "a file holds 'import', 'type', 'fn', and 'let'",
        .bails = TokenSet.initEmpty(),
    });

    assert(self.eof());
    const start = self.extraStart();
    try self.extraList(self.scratch.items[top..]);
    self.nodes.items(.data)[Node.Index.root.int()] = .{ .extra = start };
}

fn parseDecl(self: *Parse) Allocator.Error!Node.Index {
    assert(self.eof() == false);
    _ = self.eatToken(.kw_pub);
    switch (self.current()) {
        .kw_import => return self.parseImportDecl(),
        .kw_type => return self.parseTypeDecl(),
        .kw_fn => return self.parseFnDecl(),
        .kw_let => return self.parseVarDecl(),
        .kw_var => {
            try self.err(.{
                .code = .var_at_top_level,
                .span = self.here(),
                .message = "a top-level binding cannot be 'var'",
                .label = "not allowed here",
                .help = "top-level bindings are 'let', and hold a value the compiler can work out",
            });
            return self.parseVarDecl();
        },
        // `pub` with nothing it can introduce
        else => {
            try self.errExpected(.expected_declaration, "a declaration", null);
            return self.skip();
        },
    }
}

fn parseImportDecl(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_import));
    const import_token = self.nextToken();
    const path = try self.parsePath();
    return self.addUnary(.import_decl, import_token, path);
}

/// An import path, or the head of a type. Only names, never `.*`.
fn parsePath(self: *Parse) Allocator.Error!Node.Index {
    if (self.at(.ident) == false) {
        try self.errExpected(.expected_token, Token.Tag.ident.symbol(), null);
        return self.hole();
    }
    var node = try self.addLeaf(.ident);
    while (self.at(.dot)) {
        const dot = self.nextToken();
        if (self.eatToken(.ident) == null) {
            try self.errExpected(.expected_token, Token.Tag.ident.symbol(), null);
            return self.hole();
        }
        node = try self.addUnary(.field_access, dot, node);
    }
    return node;
}

/// `type Name` a unit, `= { }` a struct, `= T` an alias, which `A | B` makes a union.
fn parseTypeDecl(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_type));
    const type_token = self.nextToken();
    try self.expectToken(.ident);

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseTypeParams();
    const members_start = self.scratch.items.len;

    if (self.at(.semi) or self.at(.comma) or self.at(.eof)) {
        // a bare name, with nothing assigned, declares a unit type
        if (members_start == top) {
            return self.addNode(.{
                .tag = .unit_decl,
                .main_token = type_token,
                .data = .{ .none = {} },
            });
        }
        // type parameters with nothing assigned, so one error covers it
        try self.expectToken(.eq);
        return self.hole();
    }
    try self.expectToken(.eq);

    if (self.at(.l_brace) == false) {
        const aliased = try self.parseType();
        const start = self.extraStart();
        try self.extraList(self.scratch.items[top..members_start]);
        try self.extraNode(aliased);
        return self.addNode(.{
            .tag = .alias_decl,
            .main_token = type_token,
            .data = .{ .extra = start },
        });
    }

    const lbrace = self.eatToken(.l_brace);
    if (lbrace == null) try self.errExpected(.expected_token, Token.Tag.l_brace.symbol(), null);

    try self.parseList(.{
        .item = parseMember,
        .starts = starts_member,
        .closer = .r_brace,
        .opener = lbrace,
        .code = .expected_struct_member,
        .expected = "a field or a function",
    });

    const start = self.extraStart();
    try self.extraList(self.scratch.items[top..members_start]);
    try self.extraList(self.scratch.items[members_start..]);
    return self.addNode(.{
        .tag = .struct_decl,
        .main_token = type_token,
        .data = .{ .extra = start },
    });
}

fn parseFnDecl(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_fn));
    const fn_token = self.nextToken();
    try self.expectToken(.ident);

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseTypeParams();
    const params_start = self.scratch.items.len;

    const lparen = self.eatToken(.l_paren);
    if (lparen == null) try self.errExpected(.expected_token, Token.Tag.l_paren.symbol(), null);
    try self.parseList(.{
        .item = parseParam,
        .starts = starts_name,
        .closer = .r_paren,
        .opener = lparen,
        .code = .expected_parameter,
        .expected = "a parameter",
    });

    // nothing between the parameters and the body means it returns nothing
    const return_type: Node.OptionalIndex = if (starts_type.contains(self.current()))
        (try self.parseType()).toOptional()
    else
        .none;

    const body = try self.parseBlock();

    const start = self.extraStart();
    try self.extraList(self.scratch.items[top..params_start]);
    try self.extraList(self.scratch.items[params_start..]);
    try self.extraOpt(return_type);
    try self.extraNode(body);
    return self.addNode(.{
        .tag = .fn_decl,
        .main_token = fn_token,
        .data = .{ .extra = start },
    });
}

fn parseTypeParams(self: *Parse) Allocator.Error!void {
    assert(self.scratch.items.len < self.nodes.len + 1);
    const lbracket = self.eatToken(.l_bracket) orelse return;

    const top = self.scratch.items.len;
    try self.parseList(.{
        .item = parseTypeParam,
        .starts = starts_name,
        .closer = .r_bracket,
        .opener = lbracket,
        .code = .expected_parameter,
        .expected = "a type parameter",
    });

    assert(self.scratch.items.len >= top);
    if (self.scratch.items.len - top > type_params_max) try self.errTypeParams(lbracket, top);
    assert(self.scratch.items.len - top <= type_params_max);
}

fn errTypeParams(self: *Parse, lbracket: Token.Index, top: usize) Allocator.Error!void {
    @branchHint(.cold);
    assert(self.scratch.items.len - top > type_params_max);

    try self.err(.{
        .code = .too_many_type_params,
        .span = self.spanOf(lbracket),
        .message = try self.fmt("this declares more than {d} type parameters", .{type_params_max}),
        .label = "too many",
        .help = "a declaration this generic is asking for a struct of its own",
    });
    self.scratch.shrinkRetainingCapacity(top + type_params_max);
}

fn parseTypeParam(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.ident));
    return self.addLeaf(.type_param);
}

fn parseParam(self: *Parse) Allocator.Error!Node.Index {
    return self.parseTypedName(.param);
}

fn parseField(self: *Parse) Allocator.Error!Node.Index {
    return self.parseTypedName(.field);
}

/// `name: Type`, a parameter or a field.
fn parseTypedName(self: *Parse, node_tag: Node.Tag) Allocator.Error!Node.Index {
    assert(node_tag == .param or node_tag == .field);
    assert(self.at(.ident));

    const name = self.nextToken();
    try self.expectToken(.colon);
    const type_expr = try self.parseType();
    return self.addUnary(node_tag, name, type_expr);
}

/// A struct body holds fields and functions, and `pub` introduces a function.
fn parseMember(self: *Parse) Allocator.Error!Node.Index {
    assert(starts_member.contains(self.current()));
    if (self.at(.ident)) return self.parseField();

    _ = self.eatToken(.kw_pub);
    if (self.at(.kw_fn)) return self.parseFnDecl();
    try self.errExpected(.expected_struct_member, "a function after 'pub'", null);
    return self.hole();
}

// statements

fn parseBlock(self: *Parse) Allocator.Error!Node.Index {
    if (self.at(.l_brace) == false) {
        try self.errExpected(.expected_token, Token.Tag.l_brace.symbol(), null);
        return self.hole();
    }
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    const lbrace = self.nextToken();
    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseStatement,
        .starts = starts_stmt,
        .closer = .r_brace,
        .opener = lbrace,
        .code = .expected_statement,
        .expected = "a statement",
    });

    const start = self.extraStart();
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .block,
        .main_token = lbrace,
        .data = .{ .extra = start },
    });
}

fn parseStatement(self: *Parse) Allocator.Error!Node.Index {
    assert(starts_stmt.contains(self.current()));
    switch (self.current()) {
        .kw_let, .kw_var => return self.parseVarDecl(),
        .kw_else => return self.parseStrayElse(),
        .kw_defer => {
            const defer_token = self.nextToken();
            const body = if (self.at(.l_brace))
                try self.parseBlock()
            else
                try self.parseExprStatement();
            return self.addUnary(.defer_stmt, defer_token, body);
        },
        else => return self.parseExprStatement(),
    }
}

/// Likeliest the newline that ended the `if`. The arm is read, so it reports once.
fn parseStrayElse(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_else));
    try self.err(.{
        .code = .stray_else,
        .span = self.here(),
        .message = "'else' has no 'if' to belong to",
        .label = "no 'if' here",
        .help = "an 'else' sits on the same line as the '}' that closes its 'if'",
    });
    _ = self.nextToken();
    return if (self.at(.kw_if)) self.parseIf() else self.parseBlock();
}

fn parseVarDecl(self: *Parse) Allocator.Error!Node.Index {
    const keyword = self.nextToken();
    assert(self.tags[keyword.int()] == .kw_let or self.tags[keyword.int()] == .kw_var);
    try self.expectToken(.ident);

    const type_expr: Node.OptionalIndex = if (self.eatToken(.colon) != null)
        (try self.parseType()).toOptional()
    else
        .none;

    try self.expectToken(.eq);
    const init_expr = try self.parseExpr();

    return self.addNode(.{
        .tag = .var_decl,
        .main_token = keyword,
        .data = .{ .opt_node_and_node = .{ type_expr, init_expr } },
    });
}

/// An expression, or an expression assigned into.
fn parseExprStatement(self: *Parse) Allocator.Error!Node.Index {
    const from = self.token_index;

    const lhs = try self.parseExpr();
    assert(lhs.int() < self.nodes.len);

    if (AST.assigns(self.current()) == false) return lhs;

    // `1 = x` is a shape error, so it never reaches a checker
    switch (self.nodes.items(.tag)[@intFromEnum(lhs)]) {
        .ident, .field_access, .deref, .bracket, .err => {},
        else => try self.err(.{
            .code = .invalid_assign_target,
            .span = self.spanSince(from),
            .message = "this cannot be assigned to",
            .label = "not a place",
            .help = "the left of '=' is a name, a field, an index, or a pointer written '.*'",
        }),
    }

    const op_token = self.nextToken();
    const rhs = try self.parseExpr();
    return self.addPair(.assign, op_token, lhs, rhs);
}

/// A header expression, where a block after `or` belongs to the header.
fn parseCondition(self: *Parse) Allocator.Error!Node.Index {
    const outer = self.in_condition;
    self.in_condition = true;
    defer self.in_condition = outer;
    return self.parseExpr();
}

/// No parentheses, and mandatory braces, so no arm can dangle.
fn parseIf(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_if));
    // an `else if` chain recurses with no block between
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    const if_token = self.nextToken();
    const cond = try self.parseCondition();
    const then_block = try self.parseBlock();
    const else_node: Node.OptionalIndex = if (self.eatToken(.kw_else) != null)
        (if (self.at(.kw_if)) try self.parseIf() else try self.parseBlock()).toOptional()
    else
        .none;

    const start = self.extraStart();
    try self.extraNode(cond);
    try self.extraNode(then_block);
    try self.extraOpt(else_node);
    return self.addNode(.{
        .tag = .if_expr,
        .main_token = if_token,
        .data = .{ .extra = start },
    });
}

/// `loop { }` forever, `loop cond { }` while. `else` runs when it ends on its own.
fn parseLoop(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_loop));
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    const loop_token = self.nextToken();

    var binding: Node.OptionalIndex = .none;
    var head: Node.OptionalIndex = .none;
    if (self.at(.l_brace) == false) {
        if (self.at(.ident) and self.peek(1) == .kw_in) {
            binding = (try self.addLeaf(.ident)).toOptional();
            _ = self.eatToken(.kw_in).?;
            head = (try self.parseLoopRange()).toOptional();
        } else {
            head = (try self.parseCondition()).toOptional();
        }
    }

    const body = try self.parseBlock();
    const else_node: Node.OptionalIndex = if (self.eatToken(.kw_else) != null)
        (try self.parseBlock()).toOptional()
    else
        .none;

    const start = self.extraStart();
    try self.extraOpt(binding);
    try self.extraOpt(head);
    try self.extraNode(body);
    try self.extraOpt(else_node);
    return self.addNode(.{
        .tag = .loop_expr,
        .main_token = loop_token,
        .data = .{ .extra = start },
    });
}

fn parseLoopRange(self: *Parse) Allocator.Error!Node.Index {
    const start = try self.parseCondition();
    const dot_dot = self.eatToken(.dot_dot) orelse {
        try self.errExpected(
            .expected_token,
            Token.Tag.dot_dot.symbol(),
            "a loop counts a range, as in 'loop i in 0..n'",
        );
        return self.hole();
    };
    const end = try self.parseCondition();

    return self.addNode(.{
        .tag = .range_expr,
        .main_token = dot_dot,
        .data = .{ .node_and_opt_node = .{ start, end.toOptional() } },
    });
}

/// `outer: loop`, which needs the one two-token peek the grammar has.
fn atLabeledLoop(self: *const Parse) bool {
    if (self.at(.ident) == false) return false;
    if (self.peek(1) != .colon) return false;
    return self.peek(2) == .kw_loop;
}

/// The label is not stored. `viewOf` reads it back off the tokens.
fn parseLabeledLoop(self: *Parse) Allocator.Error!Node.Index {
    assert(self.atLabeledLoop());
    _ = self.nextToken();
    _ = self.eatToken(.colon).?;
    return self.parseLoop();
}

/// `match e { ... }`. No parentheses, and mandatory braces, like `if`.
fn parseMatch(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_match));
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    const match_token = self.nextToken();
    const scrutinee = try self.parseCondition();

    if (self.at(.l_brace) == false) {
        try self.errExpected(.expected_token, Token.Tag.l_brace.symbol(), null);
        return self.hole();
    }
    const lbrace = self.nextToken();

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseMatchArm,
        .starts = starts_arm,
        .closer = .r_brace,
        .opener = lbrace,
        .code = .expected_match_arm,
        .expected = "a match arm",
        .help = "an arm is 'Member => expression', or 'else =>' for the rest",
    });

    const start = self.extraStart();
    try self.extraNode(scrutinee);
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .match_expr,
        .main_token = match_token,
        .data = .{ .extra = start },
    });
}

/// `Member => body`, `A | B => body`, or `else => body`. A label is a type, never a binder.
fn parseMatchArm(self: *Parse) Allocator.Error!Node.Index {
    assert(starts_arm.contains(self.current()));

    const label: Node.OptionalIndex = if (self.eatToken(.kw_else) != null)
        .none
    else
        (try self.parseType()).toOptional();

    const arrow = self.eatToken(.eq_arrow) orelse {
        try self.errExpected(
            .expected_token,
            Token.Tag.eq_arrow.symbol(),
            "an arm is 'Member => expression', or 'else =>' for the rest",
        );
        // the rest of the line was this arm, so the mistake reports once
        return self.skipItem(.r_brace);
    };

    // a handler block is unambiguous inside an arm
    const outer = self.in_condition;
    self.in_condition = false;
    defer self.in_condition = outer;

    const body = if (self.at(.l_brace)) try self.parseBlock() else try self.parseExpr();
    return self.addNode(.{
        .tag = .match_arm,
        .main_token = arrow,
        .data = .{ .opt_node_and_node = .{ label, body } },
    });
}

// expressions

fn parseExpr(self: *Parse) Allocator.Error!Node.Index {
    return self.parseExprPrec(1);
}

/// Precedence climbing over `AST.oper_table`.
fn parseExprPrec(self: *Parse, min_prec: u8) Allocator.Error!Node.Index {
    assert(min_prec > 0);
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    var node = try self.parsePrefixExpr();
    var banned_prec: u8 = 0;

    // `is` tests like a comparison, so it sits at that precedence
    const is_prec = comptime AST.oper_table[@intFromEnum(Token.Tag.eq_eq)].prec;

    while (true) {
        const op_tag = self.current();
        if (op_tag == .kw_is) {
            if (is_prec < min_prec) break;
            if (is_prec == banned_prec) try self.errChainedComparison();

            const is_token = self.nextToken();
            _ = self.eatToken(.kw_not);
            node = try self.addPair(.is_expr, is_token, node, try self.parseTypeMember());
            banned_prec = is_prec;
            continue;
        }

        const info = AST.oper_table[@intFromEnum(op_tag)];
        if (info.prec < min_prec) break;
        if (info.prec == banned_prec) try self.errChainedComparison();

        const op_token = self.nextToken();
        const rhs = try self.parseExprPrec(info.prec + 1);

        // a bare name and a block after `or` is the handler form
        if (op_tag == .kw_or and self.at(.l_brace) and self.in_condition == false and
            self.nodes.items(.tag)[@intFromEnum(rhs)] == .ident)
        {
            const block = try self.parseBlock();
            const start = self.extraStart();
            try self.extraNode(node);
            try self.extraNode(rhs);
            try self.extraNode(block);
            node = try self.addNode(.{
                .tag = .or_bind,
                .main_token = op_token,
                .data = .{ .extra = start },
            });
            banned_prec = 0;
            continue;
        }
        node = try self.addPair(.binary, op_token, node, rhs);

        banned_prec = if (info.assoc == .none) info.prec else 0;
    }
    return node;
}

fn parsePrefixExpr(self: *Parse) Allocator.Error!Node.Index {
    // these carry their own node instead of wrapping an operand
    switch (self.current()) {
        .kw_if => return self.parseIf(),
        .kw_loop => return self.parseLoop(),
        .kw_match => return self.parseMatch(),
        .kw_return => return self.parseReturn(),
        .kw_break, .kw_continue => return self.parseLoopExit(),
        else => {},
    }
    if (self.atLabeledLoop()) return self.parseLabeledLoop();

    if (AST.unary_table[@intFromEnum(self.current())] == null) return self.parseSuffixExpr();

    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    const op_token = self.nextToken();
    const operand = try self.parsePrefixExpr();
    return self.addUnary(.unary, op_token, operand);
}

fn parseReturn(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_return));

    const return_token = self.nextToken();
    const operand: Node.OptionalIndex = if (starts_expr.contains(self.current()))
        (try self.parseExpr()).toOptional()
    else
        .none;
    return self.addNode(.{
        .tag = .return_expr,
        .main_token = return_token,
        .data = .{ .opt_node = operand },
    });
}

/// `break` and `continue` with an optional `:label`, and `break` with an optional value.
fn parseLoopExit(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.kw_break) or self.at(.kw_continue));

    const is_break = self.at(.kw_break);
    const keyword = self.nextToken();

    if (self.eatToken(.colon) != null) {
        try self.expectToken(.ident);
    }
    if (is_break == false) {
        return self.addNode(.{
            .tag = .continue_expr,
            .main_token = keyword,
            .data = .{ .none = {} },
        });
    }

    const value: Node.OptionalIndex = if (starts_expr.contains(self.current()))
        (try self.parseExpr()).toOptional()
    else
        .none;
    return self.addNode(.{
        .tag = .break_expr,
        .main_token = keyword,
        .data = .{ .opt_node = value },
    });
}

/// Suffixes bind tighter than any operator, and each wraps the one before.
fn parseSuffixExpr(self: *Parse) Allocator.Error!Node.Index {
    var node = try self.parsePrimaryExpr();
    assert(node.int() < self.nodes.len);
    var suffixes: u32 = 0;

    while (true) {
        if (suffixes >= depth_max) return self.tooDeep();
        suffixes += 1;
        switch (self.current()) {
            .l_paren => node = try self.parseCall(node),
            .l_bracket => node = try self.parseBracket(node),
            .dot, .dot_star => node = try self.parseSelector(node) orelse return self.hole(),
            else => return node,
        }
    }
}

/// `.name` reaches a field, `.*` reaches what a pointer points at.
fn parseSelector(self: *Parse, base: Node.Index) Allocator.Error!?Node.Index {
    if (self.eatToken(.dot_star)) |star| return try self.addUnary(.deref, star, base);

    assert(self.at(.dot));
    const dot = self.nextToken();
    if (self.eatToken(.ident) != null) return try self.addUnary(.field_access, dot, base);
    if (self.at(.l_brace)) return try self.parseStructLiteral(base.toOptional(), dot);

    try self.errExpected(.expected_token, Token.Tag.ident.symbol(), null);
    // an operator cannot follow a `.`, so it is the mistake itself
    if (AST.oper_table[@intFromEnum(self.current())].prec > 0) _ = self.nextToken();
    return null;
}

fn parseCall(self: *Parse, callee: Node.Index) Allocator.Error!Node.Index {
    assert(self.at(.l_paren));
    assert(callee.int() < self.nodes.len);
    const lparen = self.nextToken();
    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseExpr,
        .starts = starts_expr,
        .closer = .r_paren,
        .opener = lparen,
        .code = .expected_expression,
        .expected = "an argument",
    });

    const start = self.extraStart();
    try self.extraNode(callee);
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .call,
        .main_token = lparen,
        .data = .{ .extra = start },
    });
}

/// `Box[i64]` and `row[0]` are one node. Only the checker can tell which.
fn parseBracket(self: *Parse, base: Node.Index) Allocator.Error!Node.Index {
    assert(self.at(.l_bracket));
    assert(base.int() < self.nodes.len);
    const lbracket = self.nextToken();
    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseBracketItem,
        .starts = starts_bracket_item,
        .closer = .r_bracket,
        .opener = lbracket,
        .code = .expected_expression,
        .expected = "a type argument or an index",
    });

    const start = self.extraStart();
    try self.extraNode(base);
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .bracket,
        .main_token = lbracket,
        .data = .{ .extra = start },
    });
}

/// Only a type opens with `*` or `[`. This is the one place a range is written.
fn parseBracketItem(self: *Parse) Allocator.Error!Node.Index {
    switch (self.current()) {
        .star, .l_bracket => return self.parseType(),
        else => {},
    }

    const start = try self.parseExpr();
    const dot_dot = self.eatToken(.dot_dot) orelse return start;

    const end: Node.OptionalIndex = if (starts_expr.contains(self.current()))
        (try self.parseExpr()).toOptional()
    else
        .none;

    return self.addNode(.{
        .tag = .range_expr,
        .main_token = dot_dot,
        .data = .{ .node_and_opt_node = .{ start, end } },
    });
}

fn parsePrimaryExpr(self: *Parse) Allocator.Error!Node.Index {
    switch (self.current()) {
        .builtin => return self.addLeaf(.builtin),
        .ident => return self.addLeaf(.ident),
        .number => return self.addLeaf(.number_literal),
        .string => return self.addLeaf(.string_literal),
        .char => return self.addLeaf(.char_literal),
        .l_bracket => return self.parseArrayLiteral(),
        // `.{ ... }` takes the struct from wherever it lands
        .dot => {
            const dot = self.nextToken();
            if (self.at(.l_brace)) return self.parseStructLiteral(.none, dot);

            try self.err(.{
                .code = .expected_expression,
                .span = self.here(),
                .message = try self.fmt("expected '{{' after '.', found {s}", .{
                    self.current().symbol(),
                }),
                .label = "not a struct literal",
                .help = "'.{ field: value }' builds the struct its context asks for",
            });

            // a name after the dot is part of the same mistake, so it reports once
            if (self.at(.ident)) _ = self.nextToken();

            return self.hole();
        },
        // parentheses group, and the tree already holds the grouping
        .l_paren => {
            const lparen = self.nextToken();
            const outer = self.in_condition;
            self.in_condition = false;
            const inner = try self.parseExpr();
            self.in_condition = outer;
            try self.expectClosing(.r_paren, lparen);
            return inner;
        },
        .invalid => {
            try self.err(.{
                .code = .invalid_bytes,
                .span = self.here(),
                .message = "these bytes are not part of the language",
                .label = "not readable as anything",
            });
            return self.skip();
        },
        else => {
            try self.errExpected(.expected_expression, "an expression", null);
            return self.hole();
        },
    }
}

/// `[a, b, c]`, which states its own length.
fn parseArrayLiteral(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.l_bracket));
    const lbracket = self.nextToken();

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseExpr,
        .starts = starts_expr,
        .closer = .r_bracket,
        .opener = lbracket,
        .code = .expected_expression,
        .expected = "an element",
    });

    const start = self.extraStart();
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .array_literal,
        .main_token = lbracket,
        .data = .{ .extra = start },
    });
}

/// `Point.{ x: 1 }`, or `.{ x: 1 }` where the type is left to the context.
fn parseStructLiteral(
    self: *Parse,
    type_expr: Node.OptionalIndex,
    dot: Token.Index,
) Allocator.Error!Node.Index {
    assert(self.at(.l_brace));
    const lbrace = self.nextToken();

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);

    try self.parseList(.{
        .item = parseFieldInit,
        .starts = starts_name,
        .closer = .r_brace,
        .opener = lbrace,
        .code = .expected_field_value,
        .expected = "'field: value'",
    });

    const start = self.extraStart();
    try self.extraOpt(type_expr);
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .struct_literal,
        .main_token = dot,
        .data = .{ .extra = start },
    });
}

fn parseFieldInit(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.ident));
    const name = self.nextToken();
    try self.expectToken(.colon);
    const value = try self.parseExpr();
    return self.addUnary(.struct_field_init, name, value);
}

// types

fn parseType(self: *Parse) Allocator.Error!Node.Index {
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    const first = try self.parseTypeMember();
    if (self.at(.pipe) == false) return first;

    const top = self.scratch.items.len;
    defer self.scratch.shrinkRetainingCapacity(top);
    try self.scratch.append(self.gpa, first);

    const first_pipe = self.eatToken(.pipe).?;
    try self.scratch.append(self.gpa, try self.parseTypeMember());
    while (self.eatToken(.pipe) != null) {
        try self.scratch.append(self.gpa, try self.parseTypeMember());
    }

    const start = self.extraStart();
    try self.extraList(self.scratch.items[top..]);
    return self.addNode(.{
        .tag = .union_type,
        .main_token = first_pipe,
        .data = .{ .extra = start },
    });
}

/// One union member, an array, a pointer, or a path. `|` binds looser, in `parseType`.
fn parseTypeMember(self: *Parse) Allocator.Error!Node.Index {
    if (self.enter() == false) return self.tooDeep();
    defer self.leave();

    switch (self.current()) {
        // `[]T` views elements, `[N]T` holds them, told apart by what follows
        .l_bracket => {
            if (self.peek(1) == .r_bracket) return self.parseSliceType();
            return self.parseArrayType();
        },
        .star => {
            const star = self.nextToken();
            _ = self.eatToken(.kw_var);
            const child = try self.parseTypeMember();
            return self.addUnary(.pointer_type, star, child);
        },
        else => return self.parseTypePath(),
    }
}

fn parseArrayType(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.l_bracket));
    const lbracket = self.nextToken();

    const length = try self.parseExpr();
    try self.expectClosing(.r_bracket, lbracket);
    const child = try self.parseTypeMember();
    return self.addPair(.array_type, lbracket, length, child);
}

fn parseSliceType(self: *Parse) Allocator.Error!Node.Index {
    assert(self.at(.l_bracket));
    assert(self.peek(1) == .r_bracket);

    const lbracket = self.nextToken();
    _ = self.nextToken();
    _ = self.eatToken(.kw_var);
    const child = try self.parseTypeMember();
    return self.addUnary(.slice_type, lbracket, child);
}

fn parseTypePath(self: *Parse) Allocator.Error!Node.Index {
    if (self.at(.ident) == false) {
        try self.errExpected(.expected_type, "a type", null);
        return self.hole();
    }
    const path = try self.parsePath();
    return if (self.at(.l_bracket)) self.parseBracket(path) else path;
}
