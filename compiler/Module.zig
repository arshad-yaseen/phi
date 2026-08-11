//! A module is one file.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Pool = @import("Pool.zig");
const Source = @import("Source.zig");
const Token = @import("Token.zig");
const handle = @import("util/handle.zig");
const spell = @import("util/spell.zig");

const Range = Compilation.Range;

/// `space:stem/stem`, so one file is one module.
key: []const u8,
source: Source,
tree: AST,
space: Space,
/// Rows in the declaration table, members included.
decls: Range,
/// Top-level names, keyed by source text, which outlives the map. Members go through their struct.
names: std.StringHashMapUnmanaged(Decl.Index),

const Module = @This();

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
};

/// Which directory a module resolves against.
pub const Space = enum { root, std };

// the names the compiler knows by spelling

pub const std_name = "std";
pub const prelude_name = "prelude";
pub const bool_name = "bool";
pub const none_name = "none";
const discard_name = "_";

/// Whether this text is the discard, which is never a name.
pub fn isDiscard(text: []const u8) bool {
    return std.mem.eql(u8, text, discard_name);
}

comptime {
    // module keys spell the space with `{t}`, so the tag is the name
    assert(std.mem.eql(u8, @tagName(Space.std), std_name));
}

/// The row is the identity everything else refers to.
pub const Decl = struct {
    module: Module.Index,
    node: AST.Node.Index,
    name: Pool.String,
    /// For a member function, the struct declaration it belongs to.
    owner: OptionalIndex,
    /// What resolution left behind, read with `aux`.
    result: u32,
    aux: u32,
    /// The zero-argument instantiation, cached for bracketless mentions.
    plain_instance: Pool.OptionalInstance,
    kind: Kind,
    state: State,
    /// Recorded at registration, so asking never re-reads the tree.
    type_params: u8,

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

    /// Stored in `aux` beside the payload.
    pub const ImportTarget = enum(u8) { module, decl };

    pub const Index = handle.Index("decl");
    pub const OptionalIndex = Decl.Index.Optional;

    /// Members sit contiguously after their struct.
    pub fn members(decl: Decl) Compilation.Range {
        assert(decl.kind == .struct_decl);
        return .{ .start = decl.result, .len = decl.aux };
    }
};

pub fn deinit(module: *Module, gpa: Allocator) void {
    module.tree.deinit(gpa);
    module.source.deinit(gpa);
    module.names.deinit(gpa);
    module.* = undefined;
}

pub fn findDecl(module: *const Module, text: []const u8) ?Decl.Index {
    return module.names.get(text);
}

/// The key without its space prefix.
pub fn displayName(module: *const Module) []const u8 {
    const colon = std.mem.indexOfScalar(u8, module.key, ':').?;
    assert(colon + 1 < module.key.len);
    return module.key[colon + 1 ..];
}

/// Parse one source and register its declarations, parse errors notwithstanding.
pub fn register(
    comp: *Compilation,
    key: []const u8,
    space: Space,
    source: Source,
) Allocator.Error!Module.Index {
    assert(key.len > 0);
    assert(comp.module_map.get(key) == null);

    const gpa = comp.gpa;
    const module = try gpa.create(Module);
    errdefer gpa.destroy(module);

    const index: Module.Index = .from(comp.modules.items.len);
    module.* = .{
        .key = key,
        .source = source,
        .tree = try AST.parse(gpa, source.bytes),
        .space = space,
        .decls = .{ .start = @intCast(comp.decls.items.len), .len = 0 },
        .names = .empty,
    };

    // the ownership boundary. past here the root object frees the module
    try comp.modules.append(gpa, module);
    try comp.module_map.put(gpa, key, index);

    // one instruction per two tree nodes, measured against bodies that lower
    try comp.insts.ensureTotalCapacity(gpa, comp.insts.len + module.tree.nodes.len / 2);

    if (module.tree.errors.len > 0) {
        try comp.adoptParseErrors(index, module.tree.errors);
    }

    try registerDecls(comp, module, index);
    module.decls.len = @intCast(comp.decls.items.len - module.decls.start);
    return index;
}

fn registerDecls(comp: *Compilation, module: *Module, index: Module.Index) Allocator.Error!void {
    const tree = &module.tree;
    const root = tree.viewOf(.root).root;

    try comp.decls.ensureUnusedCapacity(comp.gpa, root.len * 2);
    try module.names.ensureTotalCapacity(comp.gpa, @intCast(root.len));

    for (root) |node| {
        switch (tree.viewOf(node)) {
            .import_decl => |use| {
                const name_token = lastPathComponent(tree, use.path) orelse continue;
                _ = try addDecl(comp, module, index, .{
                    .kind = .import,
                    .node = node,
                    .name_token = name_token,
                });
            },
            .struct_decl => |decl| {
                const struct_index = try addDecl(comp, module, index, .{
                    .kind = .struct_decl,
                    .node = node,
                    .name_token = decl.name_token,
                    .type_params = @intCast(decl.type_params.len),
                }) orelse continue;
                try registerMembers(comp, module, index, struct_index, decl);
            },
            .alias_decl => |decl| _ = try addDecl(comp, module, index, .{
                .kind = .type_alias,
                .node = node,
                .name_token = decl.name_token,
                .type_params = @intCast(decl.type_params.len),
            }),
            .unit_decl => |decl| _ = try addDecl(comp, module, index, .{
                .kind = .unit_decl,
                .node = node,
                .name_token = decl.name_token,
            }),
            .fn_decl => |decl| _ = try addDecl(comp, module, index, .{
                .kind = if (decl.is_extern) .extern_fn else .fn_decl,
                .node = node,
                .name_token = decl.name_token,
                .type_params = @intCast(decl.type_params.len),
            }),
            .var_decl => |decl| _ = try addDecl(comp, module, index, .{
                .kind = .let,
                .node = node,
                .name_token = decl.name_token,
            }),
            // the parser puts only declarations and holes at the root
            .err => {},
            else => unreachable,
        }
    }
}

fn registerMembers(
    comp: *Compilation,
    module: *Module,
    index: Module.Index,
    struct_index: Decl.Index,
    decl: AST.View.StructDecl,
) Allocator.Error!void {
    const tree = &module.tree;
    const members_start: u32 = @intCast(comp.decls.items.len);

    for (decl.members) |member| {
        switch (tree.viewOf(member)) {
            .fn_decl => |fn_view| {
                _ = try addMember(comp, module, index, struct_index, .{
                    .kind = .fn_decl,
                    .node = member,
                    .name_token = fn_view.name_token,
                    .type_params = @intCast(fn_view.type_params.len),
                });
            },
            .field => {},
            .err => {},
            else => unreachable,
        }
    }

    comp.declPtr(struct_index).result = members_start;
    comp.declPtr(struct_index).aux = @intCast(comp.decls.items.len - members_start);
}

const NewDecl = struct {
    kind: Decl.Kind,
    node: AST.Node.Index,
    name_token: Token.Index,
    type_params: u8 = 0,
};

fn addDecl(
    comp: *Compilation,
    module: *Module,
    index: Module.Index,
    new: NewDecl,
) Allocator.Error!?Decl.Index {
    const tree = &module.tree;
    const text = tree.tokenSlice(new.name_token);
    if (tree.tokenTag(new.name_token) != .ident) return null;

    const name = try comp.pool.string(comp.gpa, text);
    const decl_index = try appendDecl(comp, index, new, name, .none);

    // a name the file cannot have binds nothing, so the map keeps the first one
    const refused: ?Compilation.Report = refused: {
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
        if (gop.found_existing) {
            const first = comp.declAt(gop.value_ptr.*);
            break :refused .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is declared twice in this file", .{text}),
                .label = "declared again here",
                .notes = try comp.notes(&.{comp.noteAt(index, first.node, "first declared here")}),
            };
        }
        gop.value_ptr.* = decl_index;
        break :refused null;
    };

    if (refused) |report| {
        try comp.reportToken(index, new.name_token, report);
        comp.declPtr(decl_index).state = .poisoned;
    }
    return decl_index;
}

fn addMember(
    comp: *Compilation,
    module: *Module,
    index: Module.Index,
    owner: Decl.Index,
    new: NewDecl,
) Allocator.Error!?Decl.Index {
    const tree = &module.tree;
    if (tree.tokenTag(new.name_token) != .ident) return null;
    const text = tree.tokenSlice(new.name_token);
    const name = try comp.pool.string(comp.gpa, text);

    // a member clashes with a field or an earlier member
    const clash: ?AST.Node.Index = clash: {
        const owner_row = comp.declAt(owner);
        const struct_view = tree.viewOf(owner_row.node).struct_decl;
        for (struct_view.members) |other| {
            if (other == new.node) break;
            const other_name = switch (tree.viewOf(other)) {
                .field => |field| field.name_token,
                .fn_decl => |member_fn| member_fn.name_token,
                .err => continue,
                else => unreachable,
            };
            if (std.mem.eql(u8, tree.tokenSlice(other_name), text)) break :clash other;
        }
        break :clash null;
    };

    const decl_index = try appendDecl(comp, index, new, name, owner.toOptional());
    if (clash) |first| {
        try comp.reportToken(index, new.name_token, .{
            .code = .redeclared,
            .message = try comp.fmt("'{s}' is declared twice in this struct", .{text}),
            .label = "declared again here",
            .notes = try comp.notes(&.{comp.noteAt(index, first, "first declared here")}),
        });
        comp.declPtr(decl_index).state = .poisoned;
    }
    return decl_index;
}

fn appendDecl(
    comp: *Compilation,
    module_index: Module.Index,
    new: NewDecl,
    name: Pool.String,
    owner: Decl.OptionalIndex,
) Allocator.Error!Decl.Index {
    if (comp.decls.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    assert(new.type_params <= AST.type_params_max);
    const index: Decl.Index = .from(comp.decls.items.len);
    try comp.decls.append(comp.gpa, .{
        .module = module_index,
        .node = new.node,
        .name = name,
        .owner = owner,
        .result = 0,
        .aux = 0,
        .plain_instance = .none,
        .kind = new.kind,
        .state = .unanalyzed,
        .type_params = new.type_params,
    });
    return index;
}

/// What an import binds, which is the last name in its path.
pub fn lastPathComponent(tree: *const AST, path: AST.Node.Index) ?Token.Index {
    return switch (tree.nodeTag(path)) {
        .ident => tree.nodeMainToken(path),
        .field_access => tree.viewOf(path).field_access.name_token,
        else => null,
    };
}

// modules on disk

const import_chain_max = 32;
const path_components_max = 32;

pub const Loaded = union(enum) { module: Module.Index, not_found, no_std };

/// Once per path. `sub` is joined from identifiers, so it stays in its space.
pub fn loadModule(comp: *Compilation, space: Space, sub: []const u8) Allocator.Error!Loaded {
    assert(sub.len > 0);

    const key = try comp.fmt("{t}:{s}", .{ space, sub });
    if (comp.module_map.get(key)) |index| {
        return .{ .module = index };
    }

    const base = switch (space) {
        .root => comp.root_dir,
        .std => comp.std_dir orelse return .no_std,
    };

    const path = try comp.fmt("{s}/{s}.phi", .{ std.mem.trimEnd(u8, base, "/\\"), sub });

    const source = comp.loader.load(comp.loader.context, comp.gpa, comp.io, path) catch |err|
        switch (err) {
            error.ReadFailed, error.SourceTooLarge => return .not_found,
            error.OutOfMemory => return error.OutOfMemory,
        };

    return .{ .module = try register(comp, key, space, source) };
}

/// A module, or a module plus one public declaration.
pub fn resolveImport(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    const decl = comp.declAt(decl_index);
    const module = comp.moduleAt(decl.module);
    const tree = &module.tree;
    const path = tree.viewOf(decl.node).import_decl.path;

    var names: [path_components_max][]const u8 = undefined;
    var nodes: [path_components_max]AST.Node.Index = undefined;
    const count = pathComponents(tree, path, &names, &nodes) orelse {
        try comp.reportNode(decl.module, path, .{
            .code = .module_not_found,
            .message = try comp.fmt("an import path nests more than {d} names deep", .{
                path_components_max,
            }),
        });
        return false;
    };
    assert(count > 0);

    var space = module.space;
    var first: u32 = 0;
    if (std.mem.eql(u8, names[0], std_name)) {
        space = .std;
        first = 1;
        if (count == 1) {
            try comp.reportNode(decl.module, path, .{
                .code = .module_not_found,
                .message = "'std' is a directory of modules, not a module",
                .label = "name one",
                .help = "'use std.mem' imports the memory module",
            });
            return false;
        }
    }

    // the whole path as a module wins, else the last name is a declaration in it
    const whole = try std.mem.join(comp.arena.allocator(), "/", names[first..count]);
    switch (try loadModule(comp, space, whole)) {
        .module => |target| {
            setImportTarget(comp, decl_index, .module, target.int());
            return true;
        },
        .no_std => return reportNoStd(comp, decl.module, path),
        .not_found => {},
    }

    if (count - first >= 2) {
        const parent = try std.mem.join(comp.arena.allocator(), "/", names[first .. count - 1]);
        switch (try loadModule(comp, space, parent)) {
            .module => |target| {
                const last = nodes[count - 1];
                const name_token = switch (tree.nodeTag(last)) {
                    .field_access => tree.viewOf(last).field_access.name_token,
                    else => tree.nodeMainToken(last),
                };
                const found = try findExported(
                    comp,
                    target,
                    names[count - 1],
                    .{ .module = decl.module, .node = last },
                    name_token,
                ) orelse return false;
                setImportTarget(comp, decl_index, .decl, found.int());
                return true;
            },
            .no_std => return reportNoStd(comp, decl.module, path),
            .not_found => {},
        }
    }

    const spelled = try std.mem.join(comp.arena.allocator(), ".", names[first..count]);
    try comp.reportNode(decl.module, path, .{
        .code = .module_not_found,
        .message = try comp.fmt("no module named '{s}'", .{spelled}),
        .label = "nothing on disk answers to this",
        .help = switch (space) {
            .root => try comp.fmt("modules live beside the root file, in '{s}'", .{
                comp.root_dir,
            }),
            .std => try comp.fmt("standard modules live in '{s}'", .{
                comp.std_dir orelse "<none>",
            }),
        },
    });
    return false;
}

fn setImportTarget(
    comp: *Compilation,
    decl_index: Decl.Index,
    target: Decl.ImportTarget,
    payload: u32,
) void {
    comp.declPtr(decl_index).aux = @intFromEnum(target);
    comp.declPtr(decl_index).result = payload;
}

pub const ImportResolved = union(enum) { module: Module.Index, decl: Decl.Index };

pub fn importTarget(comp: *const Compilation, decl_index: Decl.Index) ImportResolved {
    const decl = comp.declAt(decl_index);
    assert(decl.kind == .import);
    assert(decl.state == .done);
    return switch (@as(Decl.ImportTarget, @enumFromInt(decl.aux))) {
        .module => .{ .module = @enumFromInt(decl.result) },
        .decl => .{ .decl = @enumFromInt(decl.result) },
    };
}

/// Follows re-exports to the end. Null once reported, keyed on the origin's token.
pub fn findExported(
    comp: *Compilation,
    in: Module.Index,
    name_text: []const u8,
    origin: Compilation.Origin,
    name_token: Token.Index,
) Allocator.Error!?Decl.Index {
    var target = in;
    var remaining: u32 = import_chain_max;
    while (remaining > 0) : (remaining -= 1) {
        const module = comp.moduleAt(target);
        const found = module.findDecl(name_text) orelse {
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

        const decl = comp.declAt(found);
        if (origin.module != target and declIsPub(comp, found) == false) {
            try comp.reportToken(origin.module, name_token, .{
                .code = .private,
                .message = try comp.fmt("'{s}' is private to its file", .{name_text}),
                .label = "not public",
                .help = "mark the declaration 'pub' to reach it from another file",
                .notes = try comp.notes(&.{
                    comp.noteAt(decl.module, decl.node, "declared here"),
                }),
            });
            return null;
        }

        if (decl.kind != .import) return found;

        // a re-export. resolve it and keep walking
        try comp.ensure(.forDecl(found), origin);
        if (comp.declAt(found).state != .done) return null;
        switch (importTarget(comp, found)) {
            .decl => |next| {
                const next_decl = comp.declAt(next);
                if (next_decl.kind != .import) return next;
                target = next_decl.module;
                continue;
            },
            // a module name, where a declaration was asked for
            .module => return found,
        }
    }
    try comp.reportToken(origin.module, name_token, .{
        .code = .value_cycle,
        .message = try comp.fmt("following '{s}' crossed {d} re-exports without arriving", .{
            name_text, import_chain_max,
        }),
    });
    return null;
}

pub fn declIsPub(comp: *const Compilation, decl_index: Decl.Index) bool {
    const decl = comp.declAt(decl_index);
    const tree = comp.treeOf(decl.module);
    return switch (tree.viewOf(decl.node)) {
        .import_decl => |view| view.is_pub,
        .struct_decl => |view| view.is_pub,
        .alias_decl => |view| view.is_pub,
        .unit_decl => |view| view.is_pub,
        .fn_decl => |view| view.is_pub,
        .var_decl => |view| view.is_pub,
        else => false,
    };
}

fn reportNoStd(
    comp: *Compilation,
    module: Module.Index,
    node: AST.Node.Index,
) Allocator.Error!bool {
    try comp.reportNode(module, node, .{
        .code = .module_not_found,
        .message = "the standard library was not found",
        .label = "'std' has nowhere to point",
        .help = "pass --std <dir>, or run beside a 'lib/std' directory",
    });
    return false;
}

fn pathComponents(
    tree: *const AST,
    path: AST.Node.Index,
    names: *[path_components_max][]const u8,
    nodes: *[path_components_max]AST.Node.Index,
) ?u32 {
    var count: u32 = 0;
    var node = path;
    var depth: u32 = 0;
    // to the leftmost ident, collecting names right to left
    while (depth < path_components_max) : (depth += 1) {
        switch (tree.nodeTag(node)) {
            .ident => {
                if (count == path_components_max) return null;
                names[count] = tree.tokenSlice(tree.nodeMainToken(node));
                nodes[count] = node;
                count += 1;
                std.mem.reverse([]const u8, names[0..count]);
                std.mem.reverse(AST.Node.Index, nodes[0..count]);
                return count;
            },
            .field_access => {
                const view = tree.viewOf(node).field_access;
                if (count == path_components_max) return null;
                names[count] = tree.tokenSlice(view.name_token);
                nodes[count] = node;
                count += 1;
                node = view.lhs;
            },
            // a parse hole never reaches analysis
            else => unreachable,
        }
    }
    return null;
}

fn suggestIn(
    comp: *Compilation,
    module: *const Module,
    name: []const u8,
) Allocator.Error!?[]const u8 {
    var closest: spell.Closest = .{ .target = name };
    for (comp.declsIn(module.decls)) |decl| {
        if (decl.owner != .none) continue;
        closest.consider(comp.pool.stringText(decl.name));
    }
    return comp.didYouMean(closest);
}
