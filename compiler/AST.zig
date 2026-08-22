const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const Diagnostic = @import("Diagnostic.zig");
const Handle = @import("Handle.zig");
const Parse = @import("Parse.zig");
const Token = @import("Token.zig");
const Tokenizer = @import("Tokenizer.zig");

const AST = @This();

/// Borrowed, so the caller's `Source` must outlive the tree.
source: [:0]const u8,
tokens: Tokenizer.TokenList.Slice,
comments: []const Token,
nodes: NodeList.Slice,
extra: []const u32,
errors: []const Diagnostic,
error_text: std.heap.ArenaAllocator.State,

pub const nest_max = Parse.depth_max;
pub const type_params_max = Parse.type_params_max;

const NodeList = std.MultiArrayList(Node);

pub const ExtraIndex = Handle.Index("ast extra");

pub fn parse(gpa: Allocator, source: [:0]const u8) Allocator.Error!AST {
    const tree = try Parse.run(gpa, source);

    assert(tree.nodes.len > 0);
    assert(tree.nodeTag(.root) == .root);
    return tree;
}

pub fn deinit(tree: *AST, gpa: Allocator) void {
    assert(tree.nodes.len > 0);
    assert(tree.tokens.len > 0);

    tree.tokens.deinit(gpa);
    tree.nodes.deinit(gpa);
    gpa.free(tree.comments);
    gpa.free(tree.extra);
    tree.error_text.promote(gpa).deinit();
    tree.* = undefined;
}

pub const Node = struct {
    tag: Tag,
    /// The keyword or operator the node is named by, every other token derived.
    main_token: Token.Index,
    data: Data,

    pub const Index = enum(u32) {
        root = 0,
        _,

        pub fn from(raw: usize) Index {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(raw);
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }

        pub fn toOptional(index: Index) OptionalIndex {
            const optional: OptionalIndex = @enumFromInt(@intFromEnum(index));
            assert(optional != .none);
            return optional;
        }
    };

    pub const OptionalIndex = Handle.OptionalOf(Index);

    /// One per `View`, which is where each is documented.
    pub const Tag = @typeInfo(View).@"union".tag_type.?;

    /// Reinterpreted by `tag`. Only `viewOf` reads it.
    const Data = union {
        none: void,
        /// A second token, where `main_token` alone does not bound the node.
        token: Token.Index,
        node: Index,
        opt_node: OptionalIndex,
        node_and_node: struct { Index, Index },
        node_and_opt_node: struct { Index, OptionalIndex },
        opt_node_and_node: struct { OptionalIndex, Index },
        extra: ExtraIndex,
    };
};

comptime {
    assert(@sizeOf(Node.Tag) == 1);
    assert(@sizeOf(Node.Index) == 4);
    assert(@sizeOf(ExtraIndex) == 4);
    if (std.debug.runtime_safety == false) assert(@sizeOf(Node.Data) == 8);
}

const Fields = struct {
    extra: []const u32,
    cursor: u32,

    fn node(payload: *Fields) Node.Index {
        assert(payload.cursor < payload.extra.len);
        defer payload.cursor += 1;
        return @enumFromInt(payload.extra[payload.cursor]);
    }

    fn optNode(payload: *Fields) Node.OptionalIndex {
        assert(payload.cursor < payload.extra.len);
        defer payload.cursor += 1;
        return @enumFromInt(payload.extra[payload.cursor]);
    }

    fn list(payload: *Fields) []const Node.Index {
        assert(payload.cursor < payload.extra.len);
        const length = payload.extra[payload.cursor];
        assert(payload.cursor + 1 + length <= payload.extra.len);

        defer payload.cursor += 1 + length;
        return @ptrCast(payload.extra[payload.cursor + 1 ..][0..length]);
    }
};

pub const BinaryOp = enum {
    add,
    sub,
    mul,
    div,
    mod,
    bit_and,
    bit_or,
    bit_xor,
    shift_left,
    shift_right,
    equal,
    not_equal,
    less_than,
    less_or_equal,
    greater_than,
    greater_or_equal,
    bool_and,
    bool_or,
};

pub const UnaryOp = enum {
    negate,
    bool_not,
    bit_not,
    address_of,
};

/// `none` bans chaining, so `a < b < c` is reported rather than nested.
pub const Assoc = enum { left, none };

pub const OperInfo = struct { prec: u8, assoc: Assoc, op: BinaryOp };

/// Where `is` sits too, testing like a comparison.
pub const compare_prec = 3;

pub const oper_table: [Token.tag_count]?OperInfo = blk: {
    @setEvalBranchQuota(8000);
    var table: [Token.tag_count]?OperInfo = @splat(null);
    for (.{
        .{ Token.Tag.kw_or, 1, Assoc.left, BinaryOp.bool_or },
        .{ Token.Tag.kw_and, 2, Assoc.left, BinaryOp.bool_and },
        .{ Token.Tag.eq_eq, compare_prec, Assoc.none, BinaryOp.equal },
        .{ Token.Tag.bang_eq, compare_prec, Assoc.none, BinaryOp.not_equal },
        .{ Token.Tag.lt, compare_prec, Assoc.none, BinaryOp.less_than },
        .{ Token.Tag.lt_eq, compare_prec, Assoc.none, BinaryOp.less_or_equal },
        .{ Token.Tag.gt, compare_prec, Assoc.none, BinaryOp.greater_than },
        .{ Token.Tag.gt_eq, compare_prec, Assoc.none, BinaryOp.greater_or_equal },
        .{ Token.Tag.pipe, 4, Assoc.left, BinaryOp.bit_or },
        .{ Token.Tag.caret, 5, Assoc.left, BinaryOp.bit_xor },
        .{ Token.Tag.ampersand, 6, Assoc.left, BinaryOp.bit_and },
        .{ Token.Tag.lt_lt, 7, Assoc.left, BinaryOp.shift_left },
        .{ Token.Tag.gt_gt, 7, Assoc.left, BinaryOp.shift_right },
        .{ Token.Tag.plus, 8, Assoc.left, BinaryOp.add },
        .{ Token.Tag.minus, 8, Assoc.left, BinaryOp.sub },
        .{ Token.Tag.star, 9, Assoc.left, BinaryOp.mul },
        .{ Token.Tag.slash, 9, Assoc.left, BinaryOp.div },
        .{ Token.Tag.percent, 9, Assoc.left, BinaryOp.mod },
    }) |entry| table[@intFromEnum(entry[0])] = .{
        .prec = entry[1],
        .assoc = entry[2],
        .op = entry[3],
    };
    break :blk table;
};

pub const unary_table: [Token.tag_count]?UnaryOp = blk: {
    var table: [Token.tag_count]?UnaryOp = @splat(null);
    table[@intFromEnum(Token.Tag.minus)] = .negate;
    table[@intFromEnum(Token.Tag.kw_not)] = .bool_not;
    table[@intFromEnum(Token.Tag.tilde)] = .bit_not;
    table[@intFromEnum(Token.Tag.ampersand)] = .address_of;
    break :blk table;
};

pub const assign_table: [Token.tag_count]?BinaryOp = blk: {
    @setEvalBranchQuota(8000);
    var table: [Token.tag_count]?BinaryOp = @splat(null);
    for (.{
        .{ Token.Tag.plus_eq, BinaryOp.add },
        .{ Token.Tag.minus_eq, BinaryOp.sub },
        .{ Token.Tag.star_eq, BinaryOp.mul },
        .{ Token.Tag.slash_eq, BinaryOp.div },
        .{ Token.Tag.percent_eq, BinaryOp.mod },
        .{ Token.Tag.ampersand_eq, BinaryOp.bit_and },
        .{ Token.Tag.pipe_eq, BinaryOp.bit_or },
        .{ Token.Tag.caret_eq, BinaryOp.bit_xor },
        .{ Token.Tag.lt_lt_eq, BinaryOp.shift_left },
        .{ Token.Tag.gt_gt_eq, BinaryOp.shift_right },
    }) |entry| table[@intFromEnum(entry[0])] = entry[1];
    break :blk table;
};

pub fn assigns(tag: Token.Tag) bool {
    return tag == .eq or assign_table[@intFromEnum(tag)] != null;
}

fn infixOf(tag: Token.Tag) OperInfo {
    return oper_table[@intFromEnum(tag)] orelse unreachable;
}

fn prefixOf(tag: Token.Tag) UnaryOp {
    return unary_table[@intFromEnum(tag)] orelse unreachable;
}

comptime {
    @setEvalBranchQuota(20000);
    for (std.enums.values(Token.Tag)) |tag| {
        // an assignment never sits between two values, so a statement sees its left end
        if (assigns(tag)) assert(oper_table[@intFromEnum(tag)] == null);
    }
}

pub const View = union(enum) {
    root: []const Node.Index,
    import_decl: Import,
    struct_decl: StructDecl,
    alias_decl: AliasDecl,
    unit_decl: UnitDecl,
    fn_decl: FnDecl,
    /// Both `let` and `var`, told apart by `main_token`.
    var_decl: VarDecl,
    type_param: TypeParam,
    param: TypedName,
    field: Field,

    block: []const Node.Index,
    assign: Assign,
    defer_stmt: Node.Index,
    if_expr: If,
    loop_expr: Loop,
    break_expr: Break,
    continue_expr: ?Token.Index,
    return_expr: Node.OptionalIndex,
    match_expr: Match,
    match_arm: MatchArm,

    builtin: Token.Index,
    ident: Token.Index,
    number_literal: Token.Index,
    string_literal: Token.Index,
    multiline_string: MultilineString,
    char_literal: Token.Index,

    field_access: FieldAccess,
    deref: Node.Index,
    /// `a[x, y]`. Type arguments where `a` is generic, an index otherwise.
    bracket: Bracket,
    call: Call,
    struct_literal: StructLiteral,
    array_literal: []const Node.Index,
    range_expr: Range,
    struct_field_init: NamedValue,

    binary: Binary,
    unary: Unary,
    is_expr: Is,
    or_bind: OrBind,

    array_type: ArrayType,
    slice_type: Wrap,
    pointer_type: Wrap,
    /// `A | B`, only in type position. Members are never unions.
    union_type: []const Node.Index,

    /// A hole where parsing broke, keeping whatever parsed before it did.
    err: Node.OptionalIndex,

    /// `import a/b/c as d`, whose names sit two tokens apart over the '/'.
    pub const Import = struct {
        first_token: Token.Index,
        last_token: Token.Index,
        binding_token: Token.Index,
    };
    pub const StructDecl = struct {
        name_token: Token.Index,
        is_pub: bool,
        type_params: []const Node.Index,
        members: []const Node.Index,
    };
    pub const AliasDecl = struct {
        name_token: Token.Index,
        is_pub: bool,
        type_params: []const Node.Index,
        aliased: Node.Index,
    };
    pub const UnitDecl = struct { name_token: Token.Index, is_pub: bool };
    pub const FnDecl = struct {
        name_token: Token.Index,
        is_pub: bool,
        is_extern: bool,
        type_params: []const Node.Index,
        params: []const Node.Index,
        return_type: Node.OptionalIndex,
        body: Node.OptionalIndex,
    };
    pub const VarDecl = struct {
        name_token: Token.Index,
        is_mutable: bool,
        is_pub: bool,
        type_expr: Node.OptionalIndex,
        init_expr: Node.Index,
    };
    pub const LoopRange = struct { name: Node.Index, over: Node.Index };
    pub const TypeParam = struct { name_token: Token.Index, bound: Node.OptionalIndex };
    pub const TypedName = struct { name_token: Token.Index, type_expr: Node.Index };
    pub const Field = struct { name_token: Token.Index, is_pub: bool, type_expr: Node.Index };
    pub const NamedValue = struct { name_token: Token.Index, value: Node.Index };
    pub const Assign = struct {
        op: ?BinaryOp,
        op_token: Token.Index,
        lhs: Node.Index,
        rhs: Node.Index,
    };
    pub const If = struct {
        cond: Node.Index,
        then_block: Node.Index,
        else_node: Node.OptionalIndex,
    };
    pub const Loop = struct {
        label: ?Token.Index,
        head: LoopHead,
        body: Node.Index,
        else_node: Node.OptionalIndex,
    };
    pub const LoopHead = union(enum) {
        forever,
        cond: Node.Index,
        range: LoopRange,

        pub fn ends(head: LoopHead) bool {
            return switch (head) {
                .forever => false,
                .cond, .range => true,
            };
        }
    };
    pub const Break = struct { label: ?Token.Index, value: Node.OptionalIndex };
    pub const Match = struct { scrutinee: Node.Index, arms: []const Node.Index };
    pub const MatchArm = struct { label: Node.OptionalIndex, body: Node.Index };
    pub const StructLiteral = struct {
        type_expr: Node.OptionalIndex,
        fields: []const Node.Index,
    };
    pub const MultilineString = struct { first: Token.Index, last: Token.Index };
    pub const Bracket = struct { base: Node.Index, args: []const Node.Index };
    /// `.none` leaves the end to the base, which is asked for its length.
    pub const Range = struct { start: Node.Index, end: Node.OptionalIndex };
    pub const Call = struct { callee: Node.Index, args: []const Node.Index };
    pub const FieldAccess = struct { lhs: Node.Index, name_token: Token.Index };
    pub const ArrayType = struct { length: Node.Index, child: Node.Index };
    pub const Wrap = struct { is_mutable: bool, child: Node.Index };
    pub const Binary = struct {
        op: BinaryOp,
        op_token: Token.Index,
        lhs: Node.Index,
        rhs: Node.Index,
    };
    pub const Unary = struct { op: UnaryOp, op_token: Token.Index, operand: Node.Index };
    pub const Is = struct { negated: bool, operand: Node.Index, type_expr: Node.Index };
    pub const OrBind = struct { lhs: Node.Index, binder: Node.Index, block: Node.Index };
};

pub inline fn viewOf(tree: AST, node: Node.Index) View {
    assert(node.int() < tree.nodes.len);

    const main = tree.nodeMainToken(node);
    const data = tree.nodes.items(.data)[node.int()];
    const view = unpack(tree, tree.nodeTag(node), main, data);

    assert(std.meta.activeTag(view) == tree.nodeTag(node));
    return view;
}

inline fn unpack(tree: AST, node_tag: Node.Tag, main: Token.Index, data: Node.Data) View {
    return switch (node_tag) {
        .root => .{ .root = tree.listAt(data.extra) },
        .import_decl => .{ .import_decl = tree.importOf(main) },
        .struct_decl => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .struct_decl = .{
                .name_token = main.after(1),
                .is_pub = tree.isPub(main),
                .type_params = payload.list(),
                .members = payload.list(),
            } };
        },
        .alias_decl => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .alias_decl = .{
                .name_token = main.after(1),
                .is_pub = tree.isPub(main),
                .type_params = payload.list(),
                .aliased = payload.node(),
            } };
        },
        .unit_decl => .{ .unit_decl = .{
            .name_token = main.after(1),
            .is_pub = tree.isPub(main),
        } },
        .fn_decl => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .fn_decl = .{
                .name_token = main.after(1),
                .is_pub = tree.isPub(main),
                .is_extern = tree.isExtern(main),
                .type_params = payload.list(),
                .params = payload.list(),
                .return_type = payload.optNode(),
                .body = payload.optNode(),
            } };
        },
        .var_decl => .{ .var_decl = .{
            .name_token = main.after(1),
            .is_mutable = tree.tokenTag(main) == .kw_var,
            .is_pub = tree.isPub(main),
            .type_expr = data.opt_node_and_node[0],
            .init_expr = data.opt_node_and_node[1],
        } },
        .type_param => .{ .type_param = .{ .name_token = main, .bound = data.opt_node } },
        .param => .{ .param = .{ .name_token = main, .type_expr = data.node } },
        .field => .{ .field = .{
            .name_token = main,
            .is_pub = tree.isPub(main),
            .type_expr = data.node,
        } },

        .block => .{ .block = tree.listAt(data.extra) },
        .assign => .{
            .assign = .{
                .op = assign_table[@intFromEnum(tree.tokenTag(main))],
                .op_token = main,
                .lhs = data.node_and_node[0],
                .rhs = data.node_and_node[1],
            },
        },
        .defer_stmt => .{ .defer_stmt = data.node },
        .if_expr => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .if_expr = .{
                .cond = payload.node(),
                .then_block = payload.node(),
                .else_node = payload.optNode(),
            } };
        },
        .loop_expr => blk: {
            var payload = tree.fields(data.extra);
            const binding = payload.optNode();
            const head = payload.optNode();
            break :blk .{ .loop_expr = .{
                .label = tree.loopLabel(main),
                .head = loopHead(binding, head),
                .body = payload.node(),
                .else_node = payload.optNode(),
            } };
        },
        .break_expr => .{ .break_expr = .{
            .label = tree.exitLabel(main),
            .value = data.opt_node,
        } },
        .continue_expr => .{ .continue_expr = tree.exitLabel(main) },
        .return_expr => .{ .return_expr = data.opt_node },
        .match_expr => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .match_expr = .{
                .scrutinee = payload.node(),
                .arms = payload.list(),
            } };
        },
        .match_arm => .{ .match_arm = .{
            .label = data.opt_node_and_node[0],
            .body = data.opt_node_and_node[1],
        } },

        .builtin => .{ .builtin = main },
        .ident => .{ .ident = main },
        .number_literal => .{ .number_literal = main },
        .string_literal => .{ .string_literal = main },
        .multiline_string => .{ .multiline_string = .{ .first = main, .last = data.token } },
        .char_literal => .{ .char_literal = main },
        .field_access => .{ .field_access = .{ .lhs = data.node, .name_token = main.after(1) } },
        .deref => .{ .deref = data.node },
        .bracket => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .bracket = .{ .base = payload.node(), .args = payload.list() } };
        },
        .call => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .call = .{ .callee = payload.node(), .args = payload.list() } };
        },
        .struct_literal => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .struct_literal = .{
                .type_expr = payload.optNode(),
                .fields = payload.list(),
            } };
        },
        .array_literal => .{ .array_literal = tree.listAt(data.extra) },
        .range_expr => .{ .range_expr = .{
            .start = data.node_and_opt_node[0],
            .end = data.node_and_opt_node[1],
        } },
        .struct_field_init => .{ .struct_field_init = .{ .name_token = main, .value = data.node } },

        .binary => .{
            .binary = .{
                .op = infixOf(tree.tokenTag(main)).op,
                .op_token = main,
                .lhs = data.node_and_node[0],
                .rhs = data.node_and_node[1],
            },
        },
        .unary => .{ .unary = .{
            .op = prefixOf(tree.tokenTag(main)),
            .op_token = main,
            .operand = data.node,
        } },

        .is_expr => .{ .is_expr = .{
            .negated = tree.tokenTag(main.after(1)) == .kw_not,
            .operand = data.node_and_node[0],
            .type_expr = data.node_and_node[1],
        } },
        .or_bind => blk: {
            var payload = tree.fields(data.extra);
            break :blk .{ .or_bind = .{
                .lhs = payload.node(),
                .binder = payload.node(),
                .block = payload.node(),
            } };
        },

        .array_type => .{ .array_type = .{
            .length = data.node_and_node[0],
            .child = data.node_and_node[1],
        } },
        // the tokens are `[`, `]`, then an optional `var`
        .slice_type => .{ .slice_type = .{
            .is_mutable = tree.tokenTag(main.after(2)) == .kw_var,
            .child = data.node,
        } },
        .pointer_type => .{ .pointer_type = .{
            .is_mutable = tree.tokenTag(main.after(1)) == .kw_var,
            .child = data.node,
        } },
        .union_type => .{ .union_type = tree.listAt(data.extra) },

        .err => .{ .err = data.opt_node },
    };
}

fn fields(tree: AST, start: ExtraIndex) Fields {
    assert(@intFromEnum(start) <= tree.extra.len);
    return .{ .extra = tree.extra, .cursor = @intFromEnum(start) };
}

fn listAt(tree: AST, start: ExtraIndex) []const Node.Index {
    var payload = tree.fields(start);
    return payload.list();
}

/// The path is the tokens themselves, which `Parse` only ever leaves in this shape.
fn importOf(tree: AST, main: Token.Index) View.Import {
    const first = main.after(1);
    assert(tree.tokenTag(first) == .ident);

    var last = first;
    while (tree.tokenTag(last.after(1)) == .slash) last = last.after(2);

    const after = last.after(1);
    const binding = if (tree.tokenTag(after) == .kw_as) after.after(1) else last;
    assert(tree.tokenTag(binding) == .ident);
    return .{ .first_token = first, .last_token = last, .binding_token = binding };
}

/// `pub` sits before the keyword a declaration is named by, or before `extern`.
fn isPub(tree: AST, main: Token.Index) bool {
    assert(main.int() < tree.tokens.len);

    const keyword = if (tree.isExtern(main)) main.before(1) else main;
    if (keyword == .first) return false;
    return tree.tokenTag(keyword.before(1)) == .kw_pub;
}

fn isExtern(tree: AST, main: Token.Index) bool {
    assert(main.int() < tree.tokens.len);

    if (main == .first) return false;
    return tree.tokenTag(main.before(1)) == .kw_extern;
}

fn loopHead(binding: Node.OptionalIndex, head: Node.OptionalIndex) View.LoopHead {
    const over = head.unwrap() orelse return .forever;
    const name = binding.unwrap() orelse return .{ .cond = over };
    return .{ .range = .{ .name = name, .over = over } };
}

fn loopLabel(tree: AST, main: Token.Index) ?Token.Index {
    assert(main.int() < tree.tokens.len);

    if (main.int() < 2) return null;
    if (tree.tokenTag(main.before(1)) != .colon) return null;
    const label = main.before(2);
    if (tree.tokenTag(label) != .ident) return null;
    return label;
}

fn exitLabel(tree: AST, main: Token.Index) ?Token.Index {
    assert(main.int() < tree.tokens.len);

    if (tree.tokenTag(main.after(1)) != .colon) return null;
    const label = main.after(2);
    if (tree.tokenTag(label) != .ident) return null;
    return label;
}

pub fn nodeTag(tree: AST, node: Node.Index) Node.Tag {
    assert(node.int() < tree.nodes.len);
    return tree.nodes.items(.tag)[node.int()];
}

pub fn nodeMainToken(tree: AST, node: Node.Index) Token.Index {
    assert(node.int() < tree.nodes.len);
    return tree.nodes.items(.main_token)[node.int()];
}

pub fn commentText(tree: AST, at: Token) []const u8 {
    assert(at.start < tree.source.len);
    return tree.source[at.start..Tokenizer.endOfLine(tree.source, at.start)];
}

pub fn docsAbove(tree: AST, node: Node.Index) []const Token {
    var next = tree.tokenStart(tree.declStart(node));
    const end = std.sort.lowerBound(Token, tree.comments, next, commentOrder);

    var first = end;
    while (first > 0) {
        const at = tree.comments[first - 1];
        if (at.tag != .doc_comment) break;
        const gap = tree.source[Tokenizer.endOfLine(tree.source, at.start)..next];
        if (std.mem.indexOfNone(u8, gap, " \t\r\n") != null) break;

        next = at.start;
        first -= 1;
    }
    return tree.comments[first..end];
}

fn commentOrder(offset: u32, comment: Token) std.math.Order {
    return std.math.order(offset, comment.start);
}

fn declStart(tree: AST, node: Node.Index) Token.Index {
    const main = tree.nodeMainToken(node);
    const keyword = if (tree.isExtern(main)) main.before(1) else main;
    return if (tree.isPub(main)) keyword.before(1) else keyword;
}

/// Past the last token reads as `.eof`, because derived positions outrun broken trees.
pub fn tokenTag(tree: AST, index: Token.Index) Token.Tag {
    const tags = tree.tokens.items(.tag);
    assert(tags.len > 0);
    if (index.int() < tags.len) return tags[index.int()];
    return .eof;
}

pub fn tokenStart(tree: AST, index: Token.Index) u32 {
    const starts = tree.tokens.items(.start);
    assert(starts.len > 0);
    if (index.int() < starts.len) return starts[index.int()];
    return @intCast(tree.source.len);
}

pub fn tokenEnd(tree: AST, index: Token.Index) u32 {
    const start = tree.tokenStart(index);
    assert(start <= tree.source.len);

    const end = Tokenizer.tokenEnd(tree.source, tree.tokenTag(index), start);
    // a `.semi` inserted at end of file occupies no `;`
    return @min(end, @as(u32, @intCast(tree.source.len)));
}

pub fn tokenSlice(tree: AST, index: Token.Index) []const u8 {
    const start = tree.tokenStart(index);
    const end = tree.tokenEnd(index);

    assert(start <= end);
    assert(end <= tree.source.len);
    return tree.source[start..end];
}

pub fn nodeSpan(tree: AST, node: Node.Index) Diagnostic.Span {
    const first = edgeToken(tree, node, .leftmost);
    const last = edgeToken(tree, node, .rightmost);
    const start = tree.tokenStart(first);
    const end = tree.tokenEnd(last);
    // a hole can straddle repaired positions
    if (start > end) {
        return .{ .start = start, .end = start };
    }
    return .{ .start = start, .end = end };
}

const Edgewise = enum { leftmost, rightmost };

const Step = union(enum) { at: Token.Index, down: Node.Index };

fn lastOf(children: []const Node.Index, empty: Step) Step {
    if (children.len == 0) return empty;
    return .{ .down = children[children.len - 1] };
}

fn edgeToken(tree: AST, node: Node.Index, side: Edgewise) Token.Index {
    var current = node;
    var depth: u32 = 0;
    // a suffix chain adds a node per suffix inside every nesting level the parser allows
    const depth_cap = nest_max * nest_max;

    while (depth < depth_cap) : (depth += 1) {
        const step = switch (side) {
            .leftmost => leftStep(tree, current),
            .rightmost => rightStep(tree, current),
        };
        switch (step) {
            .at => |token| return token,
            .down => |child| current = child,
        }
    }
    return tree.nodeMainToken(current);
}

fn leftStep(tree: AST, node: Node.Index) Step {
    const main = tree.nodeMainToken(node);
    return switch (tree.viewOf(node)) {
        .root => .{ .at = .first },
        .param, .field => .{ .at = main },
        .unary => |it| .{ .at = it.op_token },
        .loop_expr => |it| .{ .at = it.label orelse main },
        .type_param, .builtin, .ident, .number_literal => .{ .at = main },
        .err => |partial| unwrapOr(partial, main),
        .string_literal, .multiline_string, .char_literal, .import_decl => .{ .at = main },
        .struct_decl, .alias_decl, .unit_decl, .fn_decl, .var_decl, .block => .{ .at = main },
        .defer_stmt, .if_expr, .return_expr, .match_expr => .{ .at = main },
        .break_expr, .continue_expr, .array_literal => .{ .at = main },
        .struct_field_init, .array_type, .slice_type, .pointer_type => .{ .at = main },
        .assign => |it| .{ .down = it.lhs },
        .binary => |it| .{ .down = it.lhs },
        .or_bind => |it| .{ .down = it.lhs },
        .is_expr => |it| .{ .down = it.operand },
        .field_access => |it| .{ .down = it.lhs },
        .deref => |operand| .{ .down = operand },
        .bracket => |it| .{ .down = it.base },
        .call => |it| .{ .down = it.callee },
        .range_expr => |it| .{ .down = it.start },
        .union_type => |members| .{ .down = members[0] },
        .struct_literal => |it| unwrapOr(it.type_expr, main),
        .match_arm => |it| unwrapOr(it.label, main.before(1)),
    };
}

fn rightStep(tree: AST, node: Node.Index) Step {
    const main = tree.nodeMainToken(node);
    return switch (tree.viewOf(node)) {
        .root, .err, .builtin, .ident => .{ .at = main },
        .number_literal, .string_literal, .char_literal, .deref => .{ .at = main },
        .type_param => |it| unwrapOr(it.bound, main),
        .unit_decl => .{ .at = main.after(1) },
        .multiline_string => |it| .{ .at = it.last },
        .field_access => |it| .{ .at = it.name_token },
        .continue_expr => |label| .{ .at = label orelse main },
        .break_expr => |it| unwrapOr(it.value, it.label orelse main),
        .range_expr => |it| unwrapOr(it.end, main),
        .return_expr => |operand| unwrapOr(operand, main),
        .import_decl => |it| .{ .at = it.binding_token },
        .alias_decl => |it| .{ .down = it.aliased },
        .fn_decl => |it| step: {
            if (it.body.unwrap()) |body| break :step .{ .down = body };
            if (it.return_type.unwrap()) |returned| break :step .{ .down = returned };
            break :step lastOf(it.params, .{ .at = main.after(1) });
        },
        .var_decl => |it| .{ .down = it.init_expr },
        .param => |it| .{ .down = it.type_expr },
        .field => |it| .{ .down = it.type_expr },
        .assign => |it| .{ .down = it.rhs },
        .binary => |it| .{ .down = it.rhs },
        .defer_stmt => |child| .{ .down = child },
        .match_arm => |it| .{ .down = it.body },
        .struct_field_init => |it| .{ .down = it.value },
        .is_expr => |it| .{ .down = it.type_expr },
        .or_bind => |it| .{ .down = it.block },
        .unary => |it| .{ .down = it.operand },
        .array_type => |it| .{ .down = it.child },
        .slice_type, .pointer_type => |it| .{ .down = it.child },
        .union_type => |members| .{ .down = members[members.len - 1] },
        .loop_expr => |it| .{ .down = it.else_node.unwrap() orelse it.body },
        .if_expr => |it| .{ .down = it.else_node.unwrap() orelse it.then_block },
        .block => |children| lastOf(children, .{ .at = main.after(1) }),
        .struct_decl => |it| lastOf(it.members, .{ .at = main.after(1) }),
        .bracket => |it| lastOf(it.args, .{ .at = main.after(1) }),
        .call => |it| lastOf(it.args, .{ .at = main.after(1) }),
        .array_literal => |elements| lastOf(elements, .{ .at = main.after(1) }),
        .struct_literal => |it| lastOf(it.fields, .{ .at = main.after(2) }),
        .match_expr => |it| lastOf(it.arms, .{ .down = it.scrutinee }),
    };
}

fn unwrapOr(optional: Node.OptionalIndex, empty: Token.Index) Step {
    const child = optional.unwrap() orelse return .{ .at = empty };
    return .{ .down = child };
}
