//! The syntax tree.

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const Diagnostic = @import("Diagnostic.zig");
const Parse = @import("Parse.zig");
const Token = @import("Token.zig");
const Tokenizer = @import("Tokenizer.zig");

const AST = @This();

/// Borrowed, so the caller's `Source` must outlive the tree.
source: [:0]const u8,
/// In source order, ending in one `.eof`. No comment is among them.
tokens: Tokenizer.TokenList.Slice,
/// In source order. Analysis never looks.
comments: []const Comment,
/// Node 0 is the root.
nodes: NodeList.Slice,
/// Read back through `Fields`.
extra: []const u32,
/// Empty when the file parsed.
errors: []const Diagnostic,
/// Backs `errors` and its strings.
error_text: std.heap.ArenaAllocator.State,

pub const nest_max = Parse.depth_max;
pub const type_params_max = Parse.type_params_max;

pub const Comment = Tokenizer.Comment;

const NodeList = std.MultiArrayList(Node);

/// Where a node's payload starts in `extra`. Internal to the parser.
pub const ExtraIndex = enum(u32) {
    _,

    pub fn from(raw: usize) ExtraIndex {
        assert(raw < std.math.maxInt(u32));
        return @enumFromInt(@as(u32, @intCast(raw)));
    }
};

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

// storage

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
            return @enumFromInt(@as(u32, @intCast(raw)));
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }

        pub fn toOptional(i: Index) OptionalIndex {
            const optional: OptionalIndex = @enumFromInt(@intFromEnum(i));
            assert(optional != .none);
            return optional;
        }
    };

    /// Four bytes, unlike `?Index`, and still forces an `unwrap()`.
    pub const OptionalIndex = enum(u32) {
        none = std.math.maxInt(u32),
        _,

        pub fn unwrap(optional: OptionalIndex) ?Index {
            if (optional == .none) return null;
            assert(@intFromEnum(optional) != @intFromEnum(OptionalIndex.none));
            return @enumFromInt(@intFromEnum(optional));
        }
    };

    pub const Tag = enum(u8) {
        root,
        import_decl,
        struct_decl,
        alias_decl,
        /// `type Name` with nothing assigned, whose only value is its name.
        unit_decl,
        fn_decl,
        /// Both `let` and `var`, told apart by `main_token`.
        var_decl,
        /// One name in a `[T, U]` list.
        type_param,
        param,
        field,

        block,
        assign,
        defer_stmt,
        if_expr,
        /// A loop, forever or while. `else` runs when it ends on its own.
        loop_expr,
        /// `break`, with an optional `:label` and an optional value.
        break_expr,
        /// `continue`, with an optional `:label`.
        continue_expr,
        return_expr,
        /// `match e { ... }`, one arm per member of a union.
        match_expr,
        /// `Member => body`, or `else => body` when no label is stored.
        match_arm,

        /// The `intrinsic` keyword, which only a `.name` call may follow.
        intrinsic,
        ident,
        number_literal,

        field_access,
        /// `p.*`, what a pointer points at.
        deref,
        /// `a[x, y]`. Type arguments where `a` is generic, an index otherwise.
        bracket,
        call,
        /// `Point.{ ... }`, or `.{ ... }` where what it lands on says the type.
        struct_literal,
        /// `[a, b, c]`, which states its own length.
        array_literal,
        struct_field_init,

        binary,
        unary,
        /// `e is T` and `e is not T`, negation read off the token after `is`.
        is_expr,
        /// `e or name { ... }`, the handler form of `or`.
        or_bind,

        /// `[N]T`, N values of one type. The length is folded by the checker.
        array_type,
        /// `[]T` and `[]var T`, a view of elements it does not own.
        slice_type,
        pointer_type,
        /// `A | B`, only in type position. Members are never unions.
        union_type,

        /// A hole where parsing failed.
        err,
    };

    /// Reinterpreted by `tag`. Only `viewOf` reads it.
    const Data = union {
        none: void,
        node: Index,
        opt_node: OptionalIndex,
        node_and_node: struct { Index, Index },
        opt_node_and_node: struct { OptionalIndex, Index },
        /// Where `Fields` starts reading.
        extra: ExtraIndex,
    };
};

comptime {
    // one view per tag, matched by name, so a missing view is a compile error
    const tags = @typeInfo(Node.Tag).@"enum".fields;
    const views = @typeInfo(View).@"union".fields;
    assert(tags.len == views.len);
    for (tags, views) |tag, view| assert(std.mem.eql(u8, tag.name, view.name));

    assert(@sizeOf(Node.Tag) == 1);
    assert(@sizeOf(Node.Index) == 4);
    assert(@sizeOf(ExtraIndex) == 4);
    if (std.debug.runtime_safety == false) assert(@sizeOf(Node.Data) == 8);
}

/// Reads a payload back in the order `Parse` wrote it.
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

// the view

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

pub const OperInfo = struct {
    /// Zero means the token is not an infix operator. One is the loosest.
    prec: u8 = 0,
    assoc: Assoc = .left,
    /// Null for the tokens whose node is not `.binary`.
    op: ?BinaryOp = null,
};

/// The one place a token maps to an infix operator.
pub const oper_table: [Token.tag_count]OperInfo = blk: {
    @setEvalBranchQuota(8000);
    var table: [Token.tag_count]OperInfo = @splat(.{});
    for (.{
        .{ Token.Tag.kw_or, 1, Assoc.left, BinaryOp.bool_or },
        .{ Token.Tag.kw_and, 2, Assoc.left, BinaryOp.bool_and },
        .{ Token.Tag.eq_eq, 3, Assoc.none, BinaryOp.equal },
        .{ Token.Tag.bang_eq, 3, Assoc.none, BinaryOp.not_equal },
        .{ Token.Tag.lt, 3, Assoc.none, BinaryOp.less_than },
        .{ Token.Tag.lt_eq, 3, Assoc.none, BinaryOp.less_or_equal },
        .{ Token.Tag.gt, 3, Assoc.none, BinaryOp.greater_than },
        .{ Token.Tag.gt_eq, 3, Assoc.none, BinaryOp.greater_or_equal },
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

/// The one place a token maps to a prefix operator.
pub const unary_table: [Token.tag_count]?UnaryOp = blk: {
    var table: [Token.tag_count]?UnaryOp = @splat(null);
    table[@intFromEnum(Token.Tag.minus)] = .negate;
    table[@intFromEnum(Token.Tag.kw_not)] = .bool_not;
    table[@intFromEnum(Token.Tag.tilde)] = .bit_not;
    table[@intFromEnum(Token.Tag.ampersand)] = .address_of;
    break :blk table;
};

/// What a compound assignment folds in. A plain `=` has none, so `assigns` decides.
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

comptime {
    @setEvalBranchQuota(20000);
    for (std.enums.values(Token.Tag)) |tag| {
        // `unpack` reads the op of every `.binary`, so an infix token must name one
        const info = oper_table[@intFromEnum(tag)];
        if (info.prec > 0) assert(info.op != null);
        // an assignment never sits between two values, so a statement sees its left end
        if (assigns(tag)) assert(info.prec == 0);
    }
}

pub const View = union(enum) {
    root: []const Node.Index,
    import_decl: Import,
    struct_decl: StructDecl,
    alias_decl: AliasDecl,
    unit_decl: UnitDecl,
    fn_decl: FnDecl,
    var_decl: VarDecl,
    type_param: Token.Index,
    param: TypedName,
    field: TypedName,

    block: []const Node.Index,
    assign: Assign,
    defer_stmt: Node.Index,
    if_expr: If,
    loop_expr: Loop,
    break_expr: Break,
    /// The label, where one is written.
    continue_expr: ?Token.Index,
    return_expr: Node.OptionalIndex,
    match_expr: Match,
    match_arm: MatchArm,

    intrinsic: Token.Index,
    ident: Token.Index,
    number_literal: Token.Index,

    field_access: FieldAccess,
    deref: Node.Index,
    bracket: Bracket,
    call: Call,
    struct_literal: StructLiteral,
    array_literal: []const Node.Index,
    struct_field_init: NamedValue,

    binary: Binary,
    unary: Unary,
    is_expr: Is,
    or_bind: OrBind,

    array_type: ArrayType,
    slice_type: Slice,
    pointer_type: Pointer,
    union_type: []const Node.Index,

    err,

    pub const Import = struct { is_pub: bool, path: Node.Index };
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
        type_params: []const Node.Index,
        params: []const Node.Index,
        /// `.none` is a function returning nothing.
        return_type: Node.OptionalIndex,
        body: Node.Index,
    };
    pub const VarDecl = struct {
        name_token: Token.Index,
        is_mutable: bool,
        is_pub: bool,
        /// `.none` when the initializer decides the type.
        type_expr: Node.OptionalIndex,
        init_expr: Node.Index,
    };
    pub const TypedName = struct { name_token: Token.Index, type_expr: Node.Index };
    pub const NamedValue = struct { name_token: Token.Index, value: Node.Index };
    pub const Assign = struct {
        op: ?BinaryOp,
        op_token: Token.Index,
        lhs: Node.Index,
        rhs: Node.Index,
    };
    /// `else_node` is a block, or another `if_expr` for `else if`.
    pub const If = struct {
        cond: Node.Index,
        then_block: Node.Index,
        else_node: Node.OptionalIndex,
    };
    /// `cond` is `.none` for a loop that runs until a `break`.
    pub const Loop = struct {
        label: ?Token.Index,
        cond: Node.OptionalIndex,
        body: Node.Index,
        else_node: Node.OptionalIndex,
    };
    pub const Break = struct { label: ?Token.Index, value: Node.OptionalIndex };
    pub const Match = struct { scrutinee: Node.Index, arms: []const Node.Index };
    /// `label` is `.none` for the `else` arm.
    pub const MatchArm = struct { label: Node.OptionalIndex, body: Node.Index };
    pub const StructLiteral = struct {
        /// `.none` where the literal takes the type from where it lands.
        type_expr: Node.OptionalIndex,
        fields: []const Node.Index,
    };
    pub const Bracket = struct { base: Node.Index, args: []const Node.Index };
    pub const Call = struct { callee: Node.Index, args: []const Node.Index };
    pub const FieldAccess = struct { lhs: Node.Index, name_token: Token.Index };
    pub const ArrayType = struct { length: Node.Index, child: Node.Index };
    pub const Slice = struct { is_mutable: bool, child: Node.Index };
    pub const Pointer = struct { is_mutable: bool, child: Node.Index };
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

    // the comptime block proves the two tag orders align
    assert(@intFromEnum(view) == @intFromEnum(tree.nodeTag(node)));
    return view;
}

inline fn unpack(tree: AST, node_tag: Node.Tag, main: Token.Index, data: Node.Data) View {
    return switch (node_tag) {
        .root => .{ .root = tree.listAt(data.extra) },
        .import_decl => .{ .import_decl = .{ .is_pub = tree.isPub(main), .path = data.node } },
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
                .type_params = payload.list(),
                .params = payload.list(),
                .return_type = payload.optNode(),
                .body = payload.node(),
            } };
        },
        .var_decl => .{ .var_decl = .{
            .name_token = main.after(1),
            .is_mutable = tree.tokenTag(main) == .kw_var,
            .is_pub = tree.isPub(main),
            .type_expr = data.opt_node_and_node[0],
            .init_expr = data.opt_node_and_node[1],
        } },
        .type_param => .{ .type_param = main },
        .param => .{ .param = .{ .name_token = main, .type_expr = data.node } },
        .field => .{ .field = .{ .name_token = main, .type_expr = data.node } },

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
            break :blk .{ .loop_expr = .{
                .label = tree.loopLabel(main),
                .cond = payload.optNode(),
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

        .intrinsic => .{ .intrinsic = main },
        .ident => .{ .ident = main },
        .number_literal => .{ .number_literal = main },
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
        .struct_field_init => .{ .struct_field_init = .{ .name_token = main, .value = data.node } },

        .binary => .{
            .binary = .{
                // `.binary` is built only for tokens the table names
                .op = oper_table[@intFromEnum(tree.tokenTag(main))].op.?,
                .op_token = main,
                .lhs = data.node_and_node[0],
                .rhs = data.node_and_node[1],
            },
        },
        .unary => .{ .unary = .{
            .op = unary_table[@intFromEnum(tree.tokenTag(main))].?,
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

        .err => .err,
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

/// `pub` is always the token before the keyword a declaration is named by.
fn isPub(tree: AST, main: Token.Index) bool {
    assert(main.int() < tree.tokens.len);

    if (main == .first) return false;
    return tree.tokenTag(main.before(1)) == .kw_pub;
}

/// The `outer` of `outer: loop`, read off the tokens before the keyword.
fn loopLabel(tree: AST, main: Token.Index) ?Token.Index {
    assert(main.int() < tree.tokens.len);

    if (main.int() < 2) return null;
    if (tree.tokenTag(main.before(1)) != .colon) return null;
    const label = main.before(2);
    if (tree.tokenTag(label) != .ident) return null;
    return label;
}

/// The `outer` of `break :outer`, read off the tokens after the keyword.
fn exitLabel(tree: AST, main: Token.Index) ?Token.Index {
    assert(main.int() < tree.tokens.len);

    if (tree.tokenTag(main.after(1)) != .colon) return null;
    const label = main.after(2);
    if (tree.tokenTag(label) != .ident) return null;
    return label;
}

// nodes

pub fn nodeTag(tree: AST, node: Node.Index) Node.Tag {
    assert(node.int() < tree.nodes.len);
    return tree.nodes.items(.tag)[node.int()];
}

pub fn nodeMainToken(tree: AST, node: Node.Index) Token.Index {
    assert(node.int() < tree.nodes.len);
    return tree.nodes.items(.main_token)[node.int()];
}

// comments

pub fn commentText(tree: AST, at: Comment) []const u8 {
    assert(at.start < tree.source.len);
    return tree.source[at.start..Tokenizer.endOfLine(tree.source, at.start)];
}

/// The `///` run directly above a declaration, with only space between.
pub fn docsAbove(tree: AST, node: Node.Index) []const Comment {
    var next = tree.tokenStart(tree.declStart(node));
    // comments are in source order, so the run ends where the declaration starts
    const end = std.sort.lowerBound(Comment, tree.comments, next, commentOrder);

    var first = end;
    while (first > 0) {
        const at = tree.comments[first - 1];
        if (at.kind != .doc) break;
        const gap = tree.source[Tokenizer.endOfLine(tree.source, at.start)..next];
        if (std.mem.indexOfNone(u8, gap, " \t\r\n") != null) break;

        next = at.start;
        first -= 1;
    }
    return tree.comments[first..end];
}

fn commentOrder(offset: u32, comment: Comment) std.math.Order {
    return std.math.order(offset, comment.start);
}

fn declStart(tree: AST, node: Node.Index) Token.Index {
    const main = tree.nodeMainToken(node);
    return if (tree.isPub(main)) main.before(1) else main;
}

// tokens

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

// spans

/// From the leftmost token start to the rightmost child end.
pub fn nodeSpan(tree: AST, node: Node.Index) Diagnostic.Span {
    const first = edgeToken(tree, node, .leftmost);
    const last = edgeToken(tree, node, .rightmost);
    const start = tree.tokenStart(first);
    const end = tree.tokenEnd(last);
    if (start > end) {
        // a hole can straddle repaired positions
        return .{ .start = start, .end = start };
    }
    return .{ .start = start, .end = end };
}

const Edgewise = enum { leftmost, rightmost };

/// Down one side of a node to the token that bounds it.
fn edgeToken(tree: AST, node: Node.Index, side: Edgewise) Token.Index {
    var current = node;
    var depth: u32 = 0;
    const depth_cap = 4096;

    while (depth < depth_cap) : (depth += 1) {
        const main = tree.nodeMainToken(current);
        switch (tree.viewOf(current)) {
            .root => return if (side == .leftmost) .first else main,
            .err, .type_param => return main,
            .intrinsic, .ident, .number_literal => return main,
            .break_expr => |it| switch (side) {
                .leftmost => return main,
                .rightmost => {
                    if (it.value.unwrap()) |value| {
                        current = value;
                    } else return it.label orelse main;
                },
            },
            .continue_expr => |label| switch (side) {
                .leftmost => return main,
                .rightmost => return label orelse main,
            },
            .loop_expr => |it| switch (side) {
                .leftmost => return it.label orelse main,
                .rightmost => current = it.else_node.unwrap() orelse it.body,
            },
            .import_decl => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.path,
            },
            .struct_decl => |it| switch (side) {
                .leftmost => return main,
                .rightmost => {
                    if (it.members.len > 0) {
                        current = it.members[it.members.len - 1];
                    } else return main.after(1);
                },
            },
            .alias_decl => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.aliased,
            },
            .unit_decl => return if (side == .leftmost) main else main.after(1),
            .fn_decl => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.body,
            },
            .var_decl => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.init_expr,
            },
            .param, .field => |it| switch (side) {
                .leftmost => return it.name_token,
                .rightmost => current = it.type_expr,
            },
            .block => |children| switch (side) {
                .leftmost => return main,
                .rightmost => {
                    if (children.len > 0) {
                        current = children[children.len - 1];
                    } else return main.after(1);
                },
            },
            .assign => |it| {
                current = if (side == .leftmost) it.lhs else it.rhs;
            },
            .defer_stmt => |child| switch (side) {
                .leftmost => return main,
                .rightmost => current = child,
            },
            .if_expr => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.else_node.unwrap() orelse it.then_block,
            },
            .return_expr => |operand| switch (side) {
                .leftmost => return main,
                .rightmost => current = operand.unwrap() orelse return main,
            },
            .match_expr => |it| switch (side) {
                .leftmost => return main,
                .rightmost => {
                    // recovery can leave a match with no arms
                    if (it.arms.len > 0) {
                        current = it.arms[it.arms.len - 1];
                    } else current = it.scrutinee;
                },
            },
            .match_arm => |it| switch (side) {
                .leftmost => {
                    if (it.label.unwrap()) |label| {
                        current = label;
                    } else {
                        // an arm with no label began at the `else` keyword
                        return main.before(1);
                    }
                },
                .rightmost => current = it.body,
            },
            .field_access => |it| switch (side) {
                .leftmost => current = it.lhs,
                .rightmost => return it.name_token,
            },
            .deref => |operand| switch (side) {
                .leftmost => current = operand,
                .rightmost => return main,
            },
            .bracket => |it| switch (side) {
                .leftmost => current = it.base,
                .rightmost => {
                    if (it.args.len > 0) {
                        current = it.args[it.args.len - 1];
                    } else return main.after(1);
                },
            },
            .call => |it| switch (side) {
                .leftmost => current = it.callee,
                .rightmost => {
                    if (it.args.len > 0) {
                        current = it.args[it.args.len - 1];
                    } else return main.after(1);
                },
            },
            .struct_literal => |it| switch (side) {
                // an unnamed literal begins at its own '.'
                .leftmost => current = it.type_expr.unwrap() orelse return main,
                .rightmost => {
                    if (it.fields.len > 0) {
                        current = it.fields[it.fields.len - 1];
                    } else return main.after(2);
                },
            },
            .array_literal => |elements| switch (side) {
                .leftmost => return main,
                .rightmost => {
                    if (elements.len > 0) {
                        current = elements[elements.len - 1];
                    } else return main.after(1);
                },
            },
            .struct_field_init => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.value,
            },
            .binary => |it| {
                current = if (side == .leftmost) it.lhs else it.rhs;
            },
            .is_expr => |it| {
                current = if (side == .leftmost) it.operand else it.type_expr;
            },
            .or_bind => |it| {
                current = if (side == .leftmost) it.lhs else it.block;
            },
            .unary => |it| switch (side) {
                .leftmost => return it.op_token,
                .rightmost => current = it.operand,
            },
            .array_type => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.child,
            },
            .slice_type => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.child,
            },
            .pointer_type => |it| switch (side) {
                .leftmost => return main,
                .rightmost => current = it.child,
            },
            // a union writes at least two members, so both edges exist
            .union_type => |members| current = if (side == .leftmost)
                members[0]
            else
                members[members.len - 1],
        }
    }
    return tree.nodeMainToken(current);
}
