const std = @import("std");
const assert = std.debug.assert;
const Writer = std.Io.Writer;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const IR = @import("IR.zig");
const Pool = @import("Pool.zig");
const Token = @import("Token.zig");

const Node = AST.Node;

pub fn writeType(comp: *const Compilation, writer: *Writer, index: Pool.Index) Writer.Error!void {
    var current = index;
    var depth: u32 = 0;
    const depth_cap = 64;

    while (depth < depth_cap) : (depth += 1) {
        switch (comp.pool.typeKey(current)) {
            .type_simple => |simple| return switch (simple) {
                .poison => writer.writeAll("<broken>"),
                .untyped_int => writer.writeAll("an untyped number"),
                .untyped_float => writer.writeAll("an untyped float"),
                .untyped_aggregate => writer.writeAll("an untyped array"),
                .void => writer.writeAll("nothing"),
                else => writer.writeAll(@tagName(simple)),
            },
            .type_pointer => |pointer| {
                try writer.writeAll(if (pointer.mutable) "*var " else "*");
                current = pointer.child;
            },
            .type_array => |array| {
                try writer.print("[{d}]", .{array.len});
                current = array.child;
            },
            .type_slice => |slice| {
                try writer.writeAll(if (slice.mutable) "[]var " else "[]");
                current = slice.child;
            },
            .type_struct => |instance| return writeInstance(comp, writer, instance),
            .type_unit => |decl| {
                return writer.writeAll(comp.pool.stringText(comp.declAt(decl).name));
            },
            .type_union => |members| {
                // a member is never a union, so this recursion is one level
                for (members, 0..) |member, position| {
                    if (position > 0) try writer.writeAll(" | ");
                    try writeType(comp, writer, member);
                }
                return;
            },
        }
    }
    try writer.writeAll("...");
}

pub fn writeInstance(
    comp: *const Compilation,
    writer: *Writer,
    index: Pool.Instance,
) Writer.Error!void {
    const instance = comp.instanceAt(index);
    const decl = comp.declAt(instance.decl);
    const args = comp.instanceArgs(index);

    var skip: usize = 0;
    if (decl.owner.unwrap()) |owner_index| {
        const owner = comp.declAt(owner_index);
        try writer.writeAll(comp.pool.stringText(owner.name));
        const owner_params = comp.typeParamCount(owner_index);
        skip = @min(owner_params, args.len);
        try writeArgs(comp, writer, args[0..skip]);
        try writer.writeByte('.');
    }
    try writer.writeAll(comp.pool.stringText(decl.name));
    try writeArgs(comp, writer, args[skip..]);
}

fn writeArgs(
    comp: *const Compilation,
    writer: *Writer,
    args: []const Pool.Index,
) Writer.Error!void {
    if (args.len == 0) return;
    try writer.writeByte('[');
    for (args, 0..) |arg, position| {
        if (position > 0) try writer.writeAll(", ");
        if (comp.pool.isType(arg)) {
            try writeType(comp, writer, arg);
        } else {
            try writeConstant(comp, writer, arg);
        }
    }
    try writer.writeByte(']');
}

fn writeSignature(
    comp: *const Compilation,
    writer: *Writer,
    index: Pool.Instance,
) Writer.Error!void {
    const instance = comp.instanceAt(index);
    assert(instance.rows_state == .done or instance.rows_state == .poisoned);

    try writer.writeByte('(');
    for (comp.instanceRows(index), 0..) |row, position| {
        if (position > 0) try writer.writeAll(", ");
        try writer.print("{s}: ", .{comp.pool.stringText(row.name)});
        try writeType(comp, writer, row.type);
    }
    try writer.writeByte(')');
    if (instance.type != .void_type) {
        try writer.writeByte(' ');
        try writeType(comp, writer, instance.type);
    }
}

const aggregate_shown_max = 8;

fn writeConstant(
    comp: *const Compilation,
    writer: *Writer,
    value: Pool.Index,
) Writer.Error!void {
    switch (comp.pool.valueKey(value)) {
        .poison => try writer.writeAll("<broken>"),
        .value_int => |it| {
            try writer.print("{d}", .{it.value});
            if (it.type != .untyped_int_type) {
                try writer.writeByte(':');
                try writeType(comp, writer, it.type);
            }
        },
        .value_float => |it| {
            try writer.print("{d}", .{it.value});
            if (it.type != .untyped_float_type) {
                try writer.writeByte(':');
                try writeType(comp, writer, it.type);
            }
        },
        .value_aggregate, .value_repeat => {
            const type_index = comp.pool.typeOfValue(value);
            const fields: ?[]const Compilation.Row = switch (comp.pool.keyOf(type_index)) {
                .type_struct => |instance| comp.instanceRows(instance),
                else => null,
            };
            if (fields != null) {
                try writeType(comp, writer, type_index);
                try writer.writeAll(".{ ");
            } else {
                try writer.writeByte('[');
            }

            const count = comp.pool.aggregateLen(value);
            var at: u64 = 0;
            while (at < @min(count, aggregate_shown_max)) : (at += 1) {
                if (at > 0) try writer.writeAll(", ");
                if (fields) |rows| {
                    if (at < rows.len) {
                        try writer.print("{s}: ", .{comp.pool.stringText(rows[at].name)});
                    }
                }
                try writeConstant(comp, writer, comp.pool.aggregateAt(value, at));
            }
            if (count > aggregate_shown_max) {
                try writer.print(", +{d} more", .{count - aggregate_shown_max});
            }
            if (fields != null) try writer.writeAll(" }") else try writer.writeByte(']');
        },
        .value_unit => |unit_type| try writeType(comp, writer, unit_type),
        .value_union => |it| try writeConstant(comp, writer, it.value),
        // bytes first, then the view, so storage and a view of it never print alike
        .value_slice => |it| {
            try writeConstant(comp, writer, it.data);
            try writer.writeByte(':');
            try writeType(comp, writer, it.type);
        },
    }
}

pub fn writeConstantBare(
    comp: *const Compilation,
    writer: *Writer,
    value: Pool.Index,
) Writer.Error!void {
    switch (comp.pool.valueKey(value)) {
        .value_int => |it| try writer.print("{d}", .{it.value}),
        .value_float => |it| try writer.print("{d}", .{it.value}),
        else => try writeConstant(comp, writer, value),
    }
}

const depth_max = 1024;

comptime {
    // the parser bounds how deep a tree nests, so this walk never truncates one
    assert(depth_max > AST.nest_max);
}

pub fn writeTree(ast: AST, writer: *Writer) Writer.Error!void {
    assert(ast.nodes.len > 0);
    assert(ast.nodeTag(.root) == .root);
    try node(ast, writer, .root, 0, "");
}

fn node(
    ast: AST,
    writer: *Writer,
    index: Node.Index,
    depth: u32,
    role: []const u8,
) Writer.Error!void {
    assert(index.int() < ast.nodes.len);

    try writer.splatByteAll(' ', depth * 2);
    if (role.len > 0) try writer.print("{s}: ", .{role});
    if (depth >= depth_max) return writer.writeAll("...\n");

    const view = ast.viewOf(index);
    try writer.writeAll(@tagName(view));

    const below = depth + 1;
    switch (view) {
        .root, .block, .array_literal, .union_type => |children| {
            try writer.writeByte('\n');
            for (children) |child| try node(ast, writer, child, below, "");
        },
        .import_decl => |it| {
            const from = ast.tokenStart(it.first_token);
            try writer.print(" {s}\n", .{ast.source[from..ast.tokenEnd(it.binding_token)]});
            try docs(ast, writer, index, below);
        },
        .struct_decl => |it| {
            try declHead(ast, writer, index, below, it.name_token, it.is_pub);
            for (it.type_params) |param| try node(ast, writer, param, below, "");
            for (it.members) |member| try node(ast, writer, member, below, "");
        },
        .alias_decl => |it| {
            try declHead(ast, writer, index, below, it.name_token, it.is_pub);
            for (it.type_params) |param| try node(ast, writer, param, below, "");
            try node(ast, writer, it.aliased, below, "type");
        },
        .unit_decl => |it| try declHead(ast, writer, index, below, it.name_token, it.is_pub),
        .fn_decl => |it| {
            try writer.print(" {s}", .{ast.tokenSlice(it.name_token)});
            try flag(writer, it.is_pub, "pub");
            try flag(writer, it.is_extern, "extern");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
            for (it.type_params) |param| try node(ast, writer, param, below, "");
            for (it.params) |param| try node(ast, writer, param, below, "");
            if (it.return_type.unwrap()) |returned| try node(ast, writer, returned, below, "ret");
            if (it.body.unwrap()) |body| try node(ast, writer, body, below, "body");
        },
        .var_decl => |it| {
            const keyword = if (it.is_mutable) "var" else "let";
            try writer.print(" {s} {s}", .{ ast.tokenSlice(it.name_token), keyword });
            try flag(writer, it.is_pub, "pub");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
            if (it.type_expr.unwrap()) |declared| try node(ast, writer, declared, below, "type");
            try node(ast, writer, it.init_expr, below, "init");
        },
        .type_param => |it| {
            try writer.print(" {s}\n", .{ast.tokenSlice(it.name_token)});
            if (it.bound.unwrap()) |bound| try node(ast, writer, bound, below, "bound");
        },
        .param => |it| {
            try writer.print(" {s}\n", .{ast.tokenSlice(it.name_token)});
            try docs(ast, writer, index, below);
            try node(ast, writer, it.type_expr, below, "type");
        },
        .field => |it| {
            try declHead(ast, writer, index, below, it.name_token, it.is_pub);
            try node(ast, writer, it.type_expr, below, "type");
        },

        .assign => |it| {
            try writer.print(" {s}", .{ast.tokenSlice(it.op_token)});
            try writer.writeByte('\n');
            try node(ast, writer, it.lhs, below, "lhs");
            try node(ast, writer, it.rhs, below, "rhs");
        },
        .if_expr => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.cond, below, "cond");
            try node(ast, writer, it.then_block, below, "then");
            if (it.else_node.unwrap()) |otherwise| try node(ast, writer, otherwise, below, "else");
        },
        .loop_expr => |it| {
            if (it.label) |label| try writer.print(" {s}", .{ast.tokenSlice(label)});
            try writer.writeByte('\n');
            switch (it.head) {
                .forever => {},
                .cond => |cond| try node(ast, writer, cond, below, "cond"),
                .range => |range| {
                    try node(ast, writer, range.name, below, "binds");
                    try node(ast, writer, range.over, below, "over");
                },
            }
            try node(ast, writer, it.body, below, "body");
            if (it.else_node.unwrap()) |otherwise| try node(ast, writer, otherwise, below, "else");
        },
        .break_expr => |it| {
            if (it.label) |label| try writer.print(" {s}", .{ast.tokenSlice(label)});
            try writer.writeByte('\n');
            if (it.value.unwrap()) |value| try node(ast, writer, value, below, "value");
        },
        .continue_expr => |label| {
            if (label) |token| try writer.print(" {s}", .{ast.tokenSlice(token)});
            try writer.writeByte('\n');
        },
        .match_expr => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.scrutinee, below, "on");
            for (it.arms) |arm| try node(ast, writer, arm, below, "");
        },
        .match_arm => |it| {
            try flag(writer, it.label == .none, "else");
            try writer.writeByte('\n');
            if (it.label.unwrap()) |label| try node(ast, writer, label, below, "label");
            try node(ast, writer, it.body, below, "body");
        },
        .err => try writer.writeByte('\n'),
        .return_expr => |operand| {
            try writer.writeByte('\n');
            if (operand.unwrap()) |value| try node(ast, writer, value, below, "value");
        },

        .builtin, .ident, .number_literal, .string_literal, .char_literal => |token| {
            try writer.print(" {s}\n", .{ast.tokenSlice(token)});
        },

        .multiline_string => |it| {
            try writer.writeByte('\n');
            var line = it.first;
            while (true) : (line = line.after(1)) {
                try writer.splatByteAll(' ', below * 2);
                try writer.print("{s}\n", .{ast.tokenSlice(line)});
                if (line == it.last) break;
            }
        },

        .field_access => |it| {
            try writer.print(" {s}\n", .{ast.tokenSlice(it.name_token)});
            try node(ast, writer, it.lhs, below, "lhs");
        },
        .bracket => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.base, below, "base");
            for (it.args) |arg| try node(ast, writer, arg, below, "arg");
        },
        .call => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.callee, below, "callee");
            for (it.args) |arg| try node(ast, writer, arg, below, "arg");
        },
        .struct_literal => |it| {
            try writer.writeByte('\n');
            if (it.type_expr.unwrap()) |written| try node(ast, writer, written, below, "type");
            for (it.fields) |field| try node(ast, writer, field, below, "");
        },
        .range_expr => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.start, below, "start");
            if (it.end.unwrap()) |end| try node(ast, writer, end, below, "end");
        },
        .struct_field_init => |it| {
            try writer.print(" {s}\n", .{ast.tokenSlice(it.name_token)});
            try node(ast, writer, it.value, below, "value");
        },
        .binary => |it| {
            try writer.print(" {t}\n", .{it.op});
            try node(ast, writer, it.lhs, below, "lhs");
            try node(ast, writer, it.rhs, below, "rhs");
        },
        .unary => |it| {
            try writer.print(" {t}\n", .{it.op});
            try node(ast, writer, it.operand, below, "operand");
        },
        .is_expr => |it| {
            try flag(writer, it.negated, "not");
            try writer.writeByte('\n');
            try node(ast, writer, it.operand, below, "operand");
            try node(ast, writer, it.type_expr, below, "type");
        },
        .or_bind => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.lhs, below, "lhs");
            try node(ast, writer, it.binder, below, "binds");
            try node(ast, writer, it.block, below, "handler");
        },
        .array_type => |it| {
            try writer.writeByte('\n');
            try node(ast, writer, it.length, below, "length");
            try node(ast, writer, it.child, below, "child");
        },
        .slice_type, .pointer_type => |it| {
            try flag(writer, it.is_mutable, "var");
            try writer.writeByte('\n');
            try node(ast, writer, it.child, below, "child");
        },
        .deref, .defer_stmt => |child| {
            try writer.writeByte('\n');
            try node(ast, writer, child, below, "child");
        },
    }
}

fn declHead(
    ast: AST,
    writer: *Writer,
    index: Node.Index,
    depth: u32,
    name_token: Token.Index,
    is_pub: bool,
) Writer.Error!void {
    try writer.print(" {s}", .{ast.tokenSlice(name_token)});
    try flag(writer, is_pub, "pub");
    try writer.writeByte('\n');
    try docs(ast, writer, index, depth);
}

fn docs(ast: AST, writer: *Writer, index: Node.Index, depth: u32) Writer.Error!void {
    assert(index.int() < ast.nodes.len);

    for (ast.docsAbove(index)) |comment| {
        try writer.splatByteAll(' ', depth * 2);
        try writer.print("doc {s}\n", .{ast.commentText(comment)});
    }
}

fn flag(writer: *Writer, set: bool, name: []const u8) Writer.Error!void {
    assert(name.len > 0);
    assert(name.len < 8);
    if (set) try writer.print(" {s}", .{name});
}

pub fn writeFunc(comp: *const Compilation, body: IR.Func, writer: *Writer) Writer.Error!void {
    assert(body.blocks.len > 0);

    try writer.writeAll("fn ");
    try writeInstance(comp, writer, body.instance);
    try writeSignature(comp, writer, body.instance);
    try writer.writeByte('\n');

    for (comp.funcBlocks(body), 0..) |block, block_index| {
        try writer.print("b{d}:\n", .{block_index});

        for (block.first..block.end()) |raw| try inst(comp, body, @intCast(raw), writer);
        try terminator(comp, block.terminator, writer);
    }
}

fn inst(
    comp: *const Compilation,
    body: IR.Func,
    local: u32,
    writer: *Writer,
) Writer.Error!void {
    const it = comp.instAt(body.insts.at(local));
    const data = it.data;

    try writer.print("  %{d} = {t}", .{ local, it.tag });
    switch (it.tag.payload()) {
        .name => {
            if (data.name != .empty) try writer.print(" {s}", .{comp.pool.stringText(data.name)});
        },
        .un => {
            try writer.writeByte(' ');
            try ref(comp, data.un, writer);
        },
        .bin => {
            try writer.writeByte(' ');
            try ref(comp, data.bin.lhs, writer);
            try writer.writeAll(", ");
            try ref(comp, data.bin.rhs, writer);
        },
        .field => {
            try writer.writeByte(' ');
            try ref(comp, data.field.base, writer);
            try writer.print(", .{s}", .{comp.rowName(data.field.row)});
        },
        .probe => {
            try writer.writeByte(' ');
            try ref(comp, data.probe.operand, writer);
            try writer.writeAll(", ");
            try writeType(comp, writer, data.probe.member);
        },
        .payload => try wide(comp, body, it, writer),
        .none => unreachable,
    }

    if (it.type != .void_type) {
        try writer.writeAll(" : ");
        try writeType(comp, writer, it.type);
    }
    try writer.writeByte('\n');
}

fn wide(
    comp: *const Compilation,
    body: IR.Func,
    it: IR.Inst,
    writer: *Writer,
) Writer.Error!void {
    const extra = comp.funcExtra(body);
    try writer.writeByte(' ');
    switch (it.tag) {
        .call => {
            const call = IR.callAt(extra, it.data.payload);
            try writeInstance(comp, writer, call.callee);
            try writer.writeByte('(');
            try refs(comp, call.args, writer);
            try writer.writeByte(')');
        },
        .slice_make => {
            const made = IR.sliceMakeAt(extra, it.data.payload);
            try refs(comp, &.{ made.base, made.start, made.end }, writer);
        },
        .aggregate_init => {
            const operands = IR.aggregateInitAt(extra, it.data.payload);
            const instance = switch (comp.pool.keyOf(it.type)) {
                .type_struct => |found| found,
                else => {
                    try writer.writeByte('[');
                    try refs(comp, operands, writer);
                    return writer.writeByte(']');
                },
            };
            const rows = comp.instanceAt(instance).rows;
            try writer.writeAll(".{ ");
            for (operands, 0..) |operand, position| {
                if (position > 0) try writer.writeAll(", ");
                const row: Compilation.Row.Index = .from(rows.at(@intCast(position)));
                try writer.print("{s}: ", .{comp.rowName(row)});
                try ref(comp, operand, writer);
            }
            try writer.writeAll(" }");
        },
        else => unreachable,
    }
}

fn refs(comp: *const Compilation, operands: []const IR.Ref, writer: *Writer) Writer.Error!void {
    for (operands, 0..) |operand, position| {
        if (position > 0) try writer.writeAll(", ");
        try ref(comp, operand, writer);
    }
}

fn ref(comp: *const Compilation, operand: IR.Ref, writer: *Writer) Writer.Error!void {
    assert(operand != .none);
    switch (operand.unwrap()) {
        .inst => |index| try writer.print("%{d}", .{index.int()}),
        .constant => |value| try writeConstant(comp, writer, value),
    }
}

fn terminator(
    comp: *const Compilation,
    term: IR.Terminator,
    writer: *Writer,
) Writer.Error!void {
    switch (term) {
        .jump => |target| try writer.print("  jump b{d}\n", .{target.int()}),
        .branch => |branch| {
            try writer.writeAll("  branch ");
            try ref(comp, branch.cond, writer);
            try writer.print(", b{d}, b{d}\n", .{
                branch.then_block.int(),
                branch.else_block.int(),
            });
        },
        .ret => |value| {
            if (value == .none) {
                try writer.writeAll("  return\n");
            } else {
                try writer.writeAll("  return ");
                try ref(comp, value, writer);
                try writer.writeByte('\n');
            }
        },
        .trap => try writer.writeAll("  trap\n"),
    }
}
