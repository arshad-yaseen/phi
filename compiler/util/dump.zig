const std = @import("std");
const assert = std.debug.assert;
const Writer = std.Io.Writer;

const AST = @import("../AST.zig");
const Compilation = @import("../Compilation.zig");
const IR = @import("../IR.zig");
const spell = @import("spell.zig");

const Node = AST.Node;

/// Far above anything `Parse` can build.
const depth_max = 1024;

pub fn tree(t: AST, writer: *Writer) Writer.Error!void {
    assert(t.nodes.len > 0);
    assert(t.nodeTag(.root) == .root);
    try node(t, writer, .root, 0, "");
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
        .root, .block => |children| {
            try writer.writeByte('\n');
            for (children) |child| try node(ast, writer, child, below, "");
        },
        .import_decl => |it| {
            try flag(writer, it.is_pub, "pub");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
            try node(ast, writer, it.path, below, "path");
        },
        .struct_decl => |it| {
            try writer.print(" {s}", .{ast.tokenSlice(it.name_token)});
            try flag(writer, it.is_pub, "pub");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
            for (it.type_params) |param| try node(ast, writer, param, below, "");
            for (it.members) |member| try node(ast, writer, member, below, "");
        },
        .alias_decl => |it| {
            try writer.print(" {s}", .{ast.tokenSlice(it.name_token)});
            try flag(writer, it.is_pub, "pub");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
            for (it.type_params) |param| try node(ast, writer, param, below, "");
            try node(ast, writer, it.aliased, below, "type");
        },
        .unit_decl => |it| {
            try writer.print(" {s}", .{ast.tokenSlice(it.name_token)});
            try flag(writer, it.is_pub, "pub");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
        },
        .fn_decl => |it| {
            try writer.print(" {s}", .{ast.tokenSlice(it.name_token)});
            try flag(writer, it.is_pub, "pub");
            try writer.writeByte('\n');
            try docs(ast, writer, index, below);
            for (it.type_params) |param| try node(ast, writer, param, below, "");
            for (it.params) |param| try node(ast, writer, param, below, "");
            if (it.return_type.unwrap()) |returned| try node(ast, writer, returned, below, "ret");
            try node(ast, writer, it.body, below, "body");
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
        .type_param => |token| {
            try writer.print(" {s}\n", .{ast.tokenSlice(token)});
        },
        .param, .field => |it| {
            try writer.print(" {s}\n", .{ast.tokenSlice(it.name_token)});
            try docs(ast, writer, index, below);
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
            if (it.cond.unwrap()) |cond| try node(ast, writer, cond, below, "cond");
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
        .intrinsic, .err => {
            try writer.writeByte('\n');
        },
        .return_expr => |operand| {
            try writer.writeByte('\n');
            if (operand.unwrap()) |value| try node(ast, writer, value, below, "value");
        },

        .ident, .number_literal => |token| {
            try writer.print(" {s}\n", .{ast.tokenSlice(token)});
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
            try node(ast, writer, it.type_expr, below, "type");
            for (it.fields) |field| try node(ast, writer, field, below, "");
        },
        .array_literal => |elements| {
            try writer.writeByte('\n');
            for (elements) |element| try node(ast, writer, element, below, "");
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
        .pointer_type => |it| {
            try flag(writer, it.is_mutable, "var");
            try writer.writeByte('\n');
            try node(ast, writer, it.child, below, "child");
        },
        .union_type => |members| {
            try writer.writeByte('\n');
            for (members) |member| try node(ast, writer, member, below, "");
        },
        .deref, .defer_stmt => |child| {
            try writer.writeByte('\n');
            try node(ast, writer, child, below, "child");
        },
    }
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

// the IR dump

pub fn func(comp: *const Compilation, body: IR.Func, writer: *Writer) Writer.Error!void {
    assert(body.blocks.len > 0);

    try writer.writeAll("fn ");
    try spell.writeInstance(comp, writer, body.instance);
    try spell.writeSignature(comp, writer, body.instance);
    try writer.writeByte('\n');

    for (comp.funcBlocks(body), 0..) |block, block_index| {
        assert(block.terminator != .none);
        try writer.print("b{d}:\n", .{block_index});

        for (block.first..block.end()) |raw| {
            try inst(comp, body, @intCast(raw), writer);
        }
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
    switch (it.tag) {
        .trap => {},
        .param, .local => {
            if (data.name != .empty) try writer.print(" {s}", .{comp.pool.stringText(data.name)});
        },
        .load,
        .ptr_cast,
        .union_init,
        .union_narrow,
        .negate,
        .not,
        .bit_not,
        => {
            try writer.writeByte(' ');
            try ref(comp, data.un, writer);
        },
        .union_is => {
            try writer.writeByte(' ');
            try ref(comp, data.probe.operand, writer);
            try writer.writeAll(", ");
            try spell.writeType(comp, writer, data.probe.member);
        },
        .store,
        .add,
        .sub,
        .mul,
        .div,
        .mod,
        .bit_and,
        .bit_or,
        .bit_xor,
        .shift_left,
        .shift_right,
        .cmp_eq,
        .cmp_ne,
        .cmp_lt,
        .cmp_le,
        .cmp_gt,
        .cmp_ge,
        => {
            try writer.writeByte(' ');
            try ref(comp, data.bin.lhs, writer);
            try writer.writeAll(", ");
            try ref(comp, data.bin.rhs, writer);
        },
        .field_ptr, .field_val => {
            try writer.writeByte(' ');
            try ref(comp, data.field.base, writer);
            try writer.print(", .{s}", .{comp.rowName(data.field.row)});
        },
        .call => {
            const call = IR.callAt(comp.funcExtra(body), data.payload);
            try writer.writeByte(' ');
            try spell.writeInstance(comp, writer, call.callee);
            try writer.writeByte('(');
            for (call.args, 0..) |operand, position| {
                if (position > 0) try writer.writeAll(", ");
                try ref(comp, operand, writer);
            }
            try writer.writeByte(')');
        },
        .aggregate_init => {
            const operands = IR.aggregateInitAt(comp.funcExtra(body), data.payload);
            switch (comp.pool.keyOf(it.type)) {
                .type_struct => |instance| {
                    const rows = comp.instanceAt(instance).rows;
                    try writer.writeAll(" .{ ");
                    for (operands, 0..) |operand, position| {
                        if (position > 0) try writer.writeAll(", ");
                        const row: Compilation.Row.Index = .from(rows.at(@intCast(position)));
                        try writer.print("{s}: ", .{comp.rowName(row)});
                        try ref(comp, operand, writer);
                    }
                    try writer.writeAll(" }");
                },
                else => {
                    try writer.writeAll(" [");
                    for (operands, 0..) |operand, position| {
                        if (position > 0) try writer.writeAll(", ");
                        try ref(comp, operand, writer);
                    }
                    try writer.writeByte(']');
                },
            }
        },
    }

    if (it.type != .void_type) {
        try writer.writeAll(" : ");
        try spell.writeType(comp, writer, it.type);
    }
    try writer.writeByte('\n');
}

fn ref(comp: *const Compilation, operand: IR.Ref, writer: *Writer) Writer.Error!void {
    assert(operand != .none);
    switch (operand.unwrap()) {
        .inst => |index| try writer.print("%{d}", .{index.int()}),
        .constant => |value| try spell.writeConstant(comp, writer, value),
    }
}

fn terminator(
    comp: *const Compilation,
    term: IR.Terminator,
    writer: *Writer,
) Writer.Error!void {
    switch (term) {
        // `finish` leaves every surviving block a terminator
        .none => unreachable,
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
    }
}
