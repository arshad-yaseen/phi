const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Diagnostic = @import("Diagnostic.zig");
const Handle = @import("Handle.zig");
const Pool = @import("Pool.zig");
const Source = @import("Source.zig");
const Token = @import("Token.zig");

const Closest = Diagnostic.Closest;
const Range = Compilation.Range;

/// `space:stem/stem`, so one file is one module.
key: []const u8,
source: *const Source,
tree: *const AST,
space: Space,
decls: Range,
names: std.StringHashMapUnmanaged(Decl.Index),
/// Per node, read through `answerOf` and `symbolOf`.
answers: []Pool.Index,
symbols: []Symbol,

const Module = @This();

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
};

pub const Space = enum { root, std };

/// What a name refers to. A declaring node names itself, so one lookup serves both sides.
pub const Symbol = union(enum) {
    none,
    decl: Decl.Index,
    /// A local, by the node that declares it in this module.
    local: AST.Node.Index,
    /// A field, by the struct declaring it and the node inside that struct.
    field: struct { owner: Decl.Index, node: AST.Node.Index },
    module: Module.Index,
    /// A labeled loop, by its node.
    loop: AST.Node.Index,
};

pub const std_name = "std";
pub const prelude_name = "prelude";
pub const bool_name = "bool";
pub const none_name = "none";
const discard_name = "_";

pub fn isDiscard(text: []const u8) bool {
    return std.mem.eql(u8, text, discard_name);
}

comptime {
    // module keys spell the space with `{t}`, so the tag is the name
    assert(std.mem.eql(u8, @tagName(Space.std), std_name));
}

pub const Decl = struct {
    module: Module.Index,
    node: AST.Node.Index,
    name: Pool.String,
    owner: OptionalIndex,
    /// What the unit settled, read by `kind`.
    answer: Answer,
    /// The first of `type_params` entries in `Compilation.bounds`.
    bounds: u32,
    kind: Kind,
    state: State,
    /// Recorded at registration, so asking never re-reads the tree.
    type_params: u8,

    pub const Answer = union {
        none: void,
        /// An import, the module it binds.
        module: Module.Index,
        /// An alias, the type it names.
        type: Pool.Index,
        /// A `let`, its value.
        constant: Pool.Index,
        /// A struct, the declarations it owns.
        members: Compilation.Range,
    };

    pub const Kind = enum(u8) {
        import,
        struct_decl,
        type_alias,
        unit_decl,
        let,
        fn_decl,
        extern_fn,
    };
    pub const State = enum(u8) { unanalyzed, in_progress, done, poisoned };

    pub const Index = Handle.Index("decl");
    pub const OptionalIndex = Decl.Index.Optional;

    pub fn origin(decl: Decl) Compilation.Origin {
        return .{ .module = decl.module, .node = decl.node };
    }
};

pub fn deinit(module: *Module, gpa: Allocator) void {
    module.names.deinit(gpa);
    gpa.free(module.answers);
    gpa.free(module.symbols);
    module.* = undefined;
}

pub fn findDecl(module: *const Module, text: []const u8) ?Decl.Index {
    return module.names.get(text);
}

/// A constant, or a runtime value's type. `.poison` where nothing settled.
pub fn answerOf(module: *const Module, node: AST.Node.Index) Pool.Index {
    assert(node.int() < module.answers.len);
    return module.answers[node.int()];
}

/// `.none` where the node names nothing.
pub fn symbolOf(module: *const Module, node: AST.Node.Index) Symbol {
    assert(node.int() < module.symbols.len);
    return module.symbols[node.int()];
}

pub fn record(module: *Module, node: AST.Node.Index, answer: Pool.Index) void {
    assert(node.int() < module.answers.len);
    if (answer != .poison) module.answers[node.int()] = answer;
}

pub fn bind(module: *Module, node: AST.Node.Index, symbol: Symbol) void {
    assert(node.int() < module.symbols.len);
    assert(symbol != .none);
    module.symbols[node.int()] = symbol;
}

pub fn displayName(module: *const Module) []const u8 {
    const prefix = @tagName(module.space).len + 1;
    assert(module.key[prefix - 1] == ':');
    return module.key[prefix..];
}

pub fn register(
    comp: *Compilation,
    key: []const u8,
    space: Space,
    source: *const Source,
) Allocator.Error!Module.Index {
    assert(key.len > 0);
    assert(comp.module_map.get(key) == null);

    const gpa = comp.gpa;
    const module = try gpa.create(Module);
    errdefer gpa.destroy(module);

    const answers = try gpa.alloc(Pool.Index, source.tree.nodes.len);
    errdefer gpa.free(answers);
    @memset(answers, .poison);

    const symbols = try gpa.alloc(Symbol, source.tree.nodes.len);
    errdefer gpa.free(symbols);
    @memset(symbols, .none);

    const index: Module.Index = .from(comp.modules.items.len);
    module.* = .{
        .key = key,
        .source = source,
        .tree = &source.tree,
        .space = space,
        .decls = .{ .start = @intCast(comp.decls.items.len), .len = 0 },
        .names = .empty,
        .answers = answers,
        .symbols = symbols,
    };

    // the ownership boundary. past here the root object frees the module
    try comp.modules.append(gpa, module);
    try comp.module_map.put(gpa, key, index);

    // one instruction per two tree nodes, measured against bodies that lower
    try comp.ir.insts.ensureTotalCapacity(gpa, comp.ir.insts.len + module.tree.nodes.len / 2);

    if (module.tree.errors.len > 0) try comp.adoptParseErrors(index, module.tree.errors);

    try registerDecls(comp, module, index);
    module.decls = .since(module.decls.start, comp.decls.items.len);
    return index;
}

fn registerDecls(comp: *Compilation, module: *Module, index: Module.Index) Allocator.Error!void {
    const tree = module.tree;
    const root = tree.viewOf(.root).root;

    try comp.decls.ensureUnusedCapacity(comp.gpa, root.len * 2);
    try module.names.ensureTotalCapacity(comp.gpa, @intCast(root.len));

    for (root) |node| {
        const new: NewDecl = switch (tree.viewOf(node)) {
            .import_decl => |use| .{ .kind = .import, .name_token = use.binding_token },
            .struct_decl => |decl| .{
                .kind = .struct_decl,
                .name_token = decl.name_token,
                .type_params = @intCast(decl.type_params.len),
            },
            .alias_decl => |decl| .{
                .kind = .type_alias,
                .name_token = decl.name_token,
                .type_params = @intCast(decl.type_params.len),
            },
            .unit_decl => |decl| .{ .kind = .unit_decl, .name_token = decl.name_token },
            .fn_decl => |decl| .{
                .kind = if (decl.is_extern) .extern_fn else .fn_decl,
                .name_token = decl.name_token,
                .type_params = @intCast(decl.type_params.len),
            },
            .var_decl => |decl| .{ .kind = .let, .name_token = decl.name_token },
            .err => continue,
            else => unreachable,
        };
        if (tree.tokenTag(new.name_token) != .ident) continue;
        const decl_index = try appendDecl(comp, index, node, new, .none);
        module.bind(node, .{ .decl = decl_index });
        try bindName(comp, module, index, decl_index, new);
        if (new.kind == .struct_decl) try registerMembers(comp, module, index, decl_index, node);
    }
}

fn registerMembers(
    comp: *Compilation,
    module: *Module,
    index: Module.Index,
    struct_index: Decl.Index,
    struct_node: AST.Node.Index,
) Allocator.Error!void {
    const tree = module.tree;
    const members = tree.viewOf(struct_node).struct_decl.members;
    const members_start: u32 = @intCast(comp.decls.items.len);

    for (members, 0..) |member, position| {
        const fn_view = switch (tree.viewOf(member)) {
            .fn_decl => |fn_view| fn_view,
            .field => {
                module.bind(member, .{ .field = .{ .owner = struct_index, .node = member } });
                continue;
            },
            .err => continue,
            else => unreachable,
        };
        if (tree.tokenTag(fn_view.name_token) != .ident) continue;
        const decl_index = try appendDecl(comp, index, member, .{
            .kind = .fn_decl,
            .name_token = fn_view.name_token,
            .type_params = @intCast(fn_view.type_params.len),
        }, struct_index.toOptional());
        module.bind(member, .{ .decl = decl_index });

        const text = tree.tokenSlice(fn_view.name_token);
        for (members[0..position]) |other| {
            const other_name = switch (tree.viewOf(other)) {
                .field => |field| field.name_token,
                .fn_decl => |member_fn| member_fn.name_token,
                .err => continue,
                else => unreachable,
            };
            if (std.mem.eql(u8, tree.tokenSlice(other_name), text) == false) continue;
            try poison(comp, index, decl_index, fn_view.name_token, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is declared twice in this struct", .{text}),
                .label = "declared again here",
                .notes = try comp.noteOne(index, other, "first declared here"),
            });
            break;
        }
    }

    comp.declPtr(struct_index).answer = .{
        .members = .since(members_start, comp.decls.items.len),
    };
}

const NewDecl = struct {
    kind: Decl.Kind,
    name_token: Token.Index,
    type_params: u8 = 0,
};

fn bindName(
    comp: *Compilation,
    module: *Module,
    index: Module.Index,
    decl_index: Decl.Index,
    new: NewDecl,
) Allocator.Error!void {
    const text = module.tree.tokenSlice(new.name_token);
    const refused: Diagnostic.Report = refused: {
        if (isDiscard(text)) break :refused .{
            .code = .discard_reserved,
            .message = "'_' is not a name, and only discards a value",
            .label = "not a name",
            .help = "give this declaration a real name",
        };
        if (Pool.primitiveType(text) != null) break :refused .{
            .code = .shadows,
            .message = try comp.fmt("'{s}' is already the name of a type every file can see", .{
                text,
            }),
            .label = "already taken",
            .help = "pick another name, and alias it with 'type' if you want a synonym",
        };
        const gop = module.names.getOrPutAssumeCapacity(text);
        if (gop.found_existing) break :refused .{
            .code = .redeclared,
            .message = try comp.fmt("'{s}' is declared twice in this file", .{text}),
            .label = "declared again here",
            .help = if (new.kind == .import)
                try comp.fmt("bind it under another name, as in 'as {s}_module'", .{text})
            else
                null,
            .notes = try comp.noteOne(
                index,
                comp.declAt(gop.value_ptr.*).node,
                "first declared here",
            ),
        };
        gop.value_ptr.* = decl_index;
        return;
    };
    try poison(comp, index, decl_index, new.name_token, refused);
}

fn poison(
    comp: *Compilation,
    index: Module.Index,
    decl_index: Decl.Index,
    name_token: Token.Index,
    report: Diagnostic.Report,
) Allocator.Error!void {
    @branchHint(.cold);
    try comp.reportToken(index, name_token, report);
    comp.declPtr(decl_index).state = .poisoned;
}

fn appendDecl(
    comp: *Compilation,
    module_index: Module.Index,
    node: AST.Node.Index,
    new: NewDecl,
    owner: Decl.OptionalIndex,
) Allocator.Error!Decl.Index {
    if (comp.decls.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    assert(new.type_params <= AST.type_params_max);
    const tree = comp.treeOf(module_index);
    const index: Decl.Index = .from(comp.decls.items.len);
    try comp.decls.append(comp.gpa, .{
        .module = module_index,
        .node = node,
        .name = try comp.pool.string(comp.gpa, tree.tokenSlice(new.name_token)),
        .owner = owner,
        .answer = .{ .none = {} },
        .bounds = @intCast(comp.bounds.items.len),
        .kind = new.kind,
        .state = .unanalyzed,
        .type_params = new.type_params,
    });
    try comp.bounds.appendNTimes(comp.gpa, .poison, new.type_params);
    return index;
}

fn spaceDir(comp: *const Compilation, space: Space) ?[]const u8 {
    return switch (space) {
        .root => comp.rootDir(),
        .std => comp.options.std_dir,
    };
}

pub fn loadModule(comp: *Compilation, space: Space, sub: []const u8) Allocator.Error!?Module.Index {
    assert(sub.len > 0);

    const key = try comp.fmt("{t}:{s}", .{ space, sub });
    if (comp.module_map.get(key)) |index| return index;

    const base = spaceDir(comp, space) orelse return null;
    const path = try comp.fmt("{s}/{s}.phi", .{ std.mem.trimEnd(u8, base, "/\\"), sub });
    const source = comp.sources.load(path) catch |err| switch (err) {
        error.ReadFailed, error.SourceTooLarge => return null,
        error.OutOfMemory => return error.OutOfMemory,
    };

    const index = try register(comp, key, space, source);
    assert(comp.module_map.get(key) == index);
    return index;
}

pub fn resolveImport(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    const decl = comp.declAt(decl_index);
    assert(decl.kind == .import);

    const tree = comp.treeOf(decl.module);
    const view = tree.viewOf(decl.node).import_decl;
    const in_std = std.mem.eql(u8, tree.tokenSlice(view.first_token), std_name);

    const space: Space = if (in_std) .std else .root;
    const dir = spaceDir(comp, space) orelse {
        try comp.reportToken(decl.module, view.first_token, .{
            .code = .module_not_found,
            .message = "the standard library was not found",
            .label = "'std' has nowhere to point",
            .help = "pass --std <dir>, or run beside a 'lib/std' directory",
        });
        return false;
    };
    if (in_std and view.first_token == view.last_token) {
        try comp.reportToken(decl.module, view.first_token, .{
            .code = .module_not_found,
            .message = "'std' is the standard library, not a module in it",
            .label = "name one",
            .help = "'import std/io' imports the input and output module",
        });
        return false;
    }

    const first = if (in_std) view.first_token.after(2) else view.first_token;
    const sub = try pathText(comp, tree, first, view.last_token);
    const target = try loadModule(comp, space, sub) orelse {
        try comp.reportNode(decl.module, decl.node, .{
            .code = .module_not_found,
            .message = try comp.fmt("no module named '{s}' in '{s}'", .{ sub, dir }),
            .label = "nothing on disk answers to this",
        });
        return false;
    };
    comp.declPtr(decl_index).answer = .{ .module = target };
    comp.moduleAt(decl.module).bind(decl.node, .{ .module = target });
    return true;
}

pub fn importedModule(comp: *const Compilation, decl_index: Decl.Index) Module.Index {
    const decl = comp.declAt(decl_index);
    assert(decl.kind == .import);
    assert(decl.state == .done);
    return decl.answer.module;
}

fn pathText(
    comp: *Compilation,
    tree: *const AST,
    first: Token.Index,
    last: Token.Index,
) Allocator.Error![]const u8 {
    const arena = comp.arena.allocator();

    var out: std.ArrayList(u8) = .empty;
    try out.ensureTotalCapacity(arena, 64);
    try out.appendSlice(arena, tree.tokenSlice(first));

    var token = first;
    while (token != last) {
        token = token.after(2);
        try out.append(arena, '/');
        try out.appendSlice(arena, tree.tokenSlice(token));
    }

    assert(std.mem.indexOfScalar(u8, out.items, '.') == null);
    return out.items;
}

pub fn findExported(
    comp: *Compilation,
    in: Module.Index,
    origin: Compilation.Origin,
    name_token: Token.Index,
) Allocator.Error!?Decl.Index {
    const module = comp.moduleAt(in);
    const name_text = comp.treeOf(origin.module).tokenSlice(name_token);

    const decl_index: Decl.Index = found: {
        // an import binds a name in its own file, so it is no part of what the file offers
        if (module.findDecl(name_text)) |found| {
            if (comp.declAt(found).kind != .import) break :found found;
        }
        try comp.reportToken(origin.module, name_token, .{
            .code = .no_such_member,
            .message = try comp.fmt("'{s}' has no declaration named '{s}'", .{
                module.displayName(), name_text,
            }),
            .label = "not found",
            .help = try suggestIn(comp, module, name_text),
        });
        return null;
    };

    if (origin.module != in and declIsPub(comp, decl_index) == false) {
        try comp.reportToken(origin.module, name_token, .{
            .code = .private,
            .message = try comp.fmt("'{s}' is private to its file", .{name_text}),
            .label = "not public",
            .help = "mark the declaration 'pub' to reach it from another file",
            .notes = try comp.noteOne(in, comp.declAt(decl_index).node, "declared here"),
        });
        return null;
    }
    return decl_index;
}

pub fn declIsPub(comp: *const Compilation, decl_index: Decl.Index) bool {
    const decl = comp.declAt(decl_index);
    const tree = comp.treeOf(decl.module);
    return switch (tree.viewOf(decl.node)) {
        .struct_decl => |view| view.is_pub,
        .alias_decl => |view| view.is_pub,
        .unit_decl => |view| view.is_pub,
        .fn_decl => |view| view.is_pub,
        .var_decl => |view| view.is_pub,
        else => false,
    };
}

fn suggestIn(
    comp: *Compilation,
    module: *const Module,
    name: []const u8,
) Allocator.Error!?[]const u8 {
    var closest: Closest = .{ .target = name };
    var walk = comp.ownDecls(module.decls);
    while (walk.next()) |index| {
        const decl = comp.declAt(index);
        if (decl.kind == .import) continue;
        if (declIsPub(comp, index) == false) continue;
        closest.consider(comp.pool.stringText(decl.name));
    }
    return closest.didYouMean(comp.arena.allocator());
}
