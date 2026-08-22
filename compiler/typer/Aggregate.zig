const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const Compilation = @import("../Compilation.zig");
const IR = @import("../IR.zig");
const Pool = @import("../Pool.zig");
const Resolve = @import("Resolve.zig");
const Expr = @import("Expr.zig");
const Call = @import("Call.zig");
const Place = @import("Place.zig");

const Node = AST.Node;
const Ref = IR.Ref;
const Value = Typer.Value;
const Operand = Typer.Operand;
const refOf = Typer.refOf;
const runtimeValue = Typer.runtimeValue;
const plural = Typer.plural;
const quotedList = Typer.quotedList;

pub fn elementExample(typer: *Typer, aggregate: Pool.Key.Aggregate) Allocator.Error![]const u8 {
    if (aggregate.elems.len == 0) return "u32";
    const found = typer.comp.pool.typeOfValue(aggregate.elems[0]);
    if (Pool.isUntyped(found)) return "u32";
    return typer.comp.typeName(found);
}

const range_help = "the ends of a range take each other's type, and nothing converts on its own";

pub fn checkBracketExpr(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    if (Call.baseIsNamespace(typer, view.base) == false) return checkIndexExpr(typer, node, view);

    const base = try typer.checkExpr(view.base, null);
    switch (base) {
        .named_generic => {
            const resolved = try Resolve.resolveBracketType(typer, node);
            if (resolved == .poison) return .poison;
            return .{ .named_type = resolved };
        },
        .named_fn => {
            return typer.refuse(node, .{
                .code = .not_a_function,
                .message = "a function with its type arguments is still not a value, so call it",
                .label = "missing the call",
            });
        },
        .diverged => return .diverged,
        .poison => return .poison,
        .constant, .runtime => return checkIndexExpr(typer, node, view),
        else => {
            return typer.refuse(node, .{
                .code = .generic_arguments,
                .message = "only a generic struct or function takes type arguments",
                .label = "arguments on the wrong thing",
            });
        },
    }
}

pub const Elements = struct {
    node: Node.Index,
    base: Place,
    pointer: ?Pool.Key.Pointer,
    owner: Pool.Index,
    child: Pool.Index,
    len: ?u64,
    mutable: bool,
};

const Indexed = struct {
    elements: Elements,
    ref: Ref,
    /// The element it names, where the index is known before anything runs.
    at: ?u64,
};

fn checkIndexExpr(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    const comp = typer.comp;
    if (rangeIn(typer, view)) |range| return checkSlice(typer, node, view, range);

    const indexed = try checkIndex(typer, node, view) orelse return .poison;
    if (indexed.at) |at| {
        if (indexed.elements.pointer == null) {
            if (Place.placeConstant(typer, indexed.elements.base)) |aggregate| {
                return .{ .constant = comp.pool.aggregateAt(aggregate, at) };
            }
        }
    }

    assert(typer.builder != null);
    const place = try Place.elementPlace(typer, indexed.elements, indexed.ref) orelse return .poison;
    return runtimeValue(try Place.placeValue(typer, place), place.type);
}

fn checkSlice(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.Bracket,
    range: AST.View.Range,
) Allocator.Error!Value {
    if (typer.builder == null) return typer.needRuntime(node, "making a view");

    const elements = try checkElements(typer, node, view) orelse return .poison;
    const through = try Place.elementsThrough(typer, elements) orelse return .poison;
    const bounds = try checkRange(typer, view.args[0], range, elements, through) orelse
        return .poison;

    if (Place.refIsConstant(bounds.start) == false or Place.refIsConstant(bounds.end) == false) {
        try Place.emitCheck(typer, elements.node, .order_check, bounds.start, bounds.end);
    }
    if (range.end != .none and Place.settledAgainstBase(elements, bounds.end) == false) {
        const length = try Place.baseLengthRef(typer, elements, through);
        try Place.emitCheck(typer, elements.node, .order_check, bounds.end, length);
    }

    const made = try typer.sliceOf(elements.child, through.mutable());
    const payload = try typer.emitExtra(&.{
        @intFromEnum(through.ref),
        @intFromEnum(bounds.start),
        @intFromEnum(bounds.end),
    }, &.{});
    return typer.emitValue(node, .slice_make, made, .{ .payload = payload });
}

const Bounds = struct { start: Ref, end: Ref };

fn checkRange(
    typer: *Typer,
    range_node: Node.Index,
    range: AST.View.Range,
    elements: Elements,
    through: Place,
) Allocator.Error!?Bounds {
    const start = try checkRangeEnd(typer, range.start) orelse return null;
    const end_node = range.end.unwrap() orelse range_node;
    const end = if (range.end != .none)
        try checkRangeEnd(typer, end_node) orelse return null
    else if (elements.len) |count|
        try typer.untypedInt(count)
    else
        try typer.emitOneValue(elements.node, .slice_len, .u64_type, through.ref);

    const ends = try settleEnds(
        typer,
        range_node,
        .{ .value = start, .node = range.start },
        .{ .value = end, .node = end_node },
    ) orelse return null;

    if (countOf(typer, ends.start)) |at| {
        if (at < 0) {
            try failBeforeFirst(typer, range.start, "an end of a range", at);
            return null;
        }
    }
    if (countOf(typer, ends.end)) |at| {
        if (at < 0) {
            try failBeforeFirst(typer, end_node, "an end of a range", at);
            return null;
        }
    }
    if (try rangeRunsBackwards(typer, range_node, ends.start, ends.end)) return null;
    if (countOf(typer, ends.end)) |at| {
        if (elements.len) |count| {
            if (at > count) {
                try failPastLast(typer, end_node, "this range ends at", at, elements, count);
                return null;
            }
        }
    }
    return .{ .start = refOf(ends.start), .end = refOf(ends.end) };
}

const End = struct { value: Value, node: Node.Index };

const Ends = struct { start: Value, end: Value, type: Pool.Index };

pub fn settleEnds(typer: *Typer, range_node: Node.Index, start: End, end: End) Allocator.Error!?Ends {
    const left = typer.typeOf(start.value);
    const right = typer.typeOf(end.value);
    if (Pool.isUntyped(left) == false and Pool.isUntyped(right) == false and left != right) {
        try Expr.failMixedTypes(typer, typer.tree.nodeMainToken(range_node), left, right, range_help);
        return null;
    }

    var settled = left;
    if (Pool.isUntyped(settled)) settled = right;
    if (Pool.isUntyped(settled)) settled = .u64_type;

    const first = try typer.coerce(start.value, settled, start.node);
    const second = try typer.coerce(end.value, settled, end.node);
    if (first == .poison or second == .poison) return null;
    return .{ .start = first, .end = second, .type = settled };
}

pub fn rangeRunsBackwards(
    typer: *Typer,
    range_node: Node.Index,
    start: Value,
    end: Value,
) Allocator.Error!bool {
    const low = countOf(typer, start) orelse return false;
    const high = countOf(typer, end) orelse return false;
    if (low <= high) return false;

    try typer.failToken(typer.tree.nodeMainToken(range_node), .{
        .code = .out_of_range,
        .message = try typer.comp.fmt(
            "this range starts at {d} and ends at {d}, so it runs backwards",
            .{ low, high },
        ),
        .label = "the ends cross",
        .help = "a range runs from its start up to, but not including, its end",
    });
    return true;
}

fn countOf(typer: *const Typer, value: Value) ?i128 {
    if (value != .constant) return null;
    return switch (typer.comp.pool.keyOf(value.constant)) {
        .value_int => |it| it.value,
        else => null,
    };
}

fn failBeforeFirst(
    typer: *Typer,
    node: Node.Index,
    what: []const u8,
    at: i128,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .out_of_range,
        .message = try typer.comp.fmt("{s} counts from zero, and this one is {d}", .{ what, at }),
        .label = "before the first element",
    });
}

fn failPastLast(
    typer: *Typer,
    node: Node.Index,
    lead: []const u8,
    at: i128,
    elements: Elements,
    count: u64,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .out_of_range,
        .message = try typer.comp.fmt("{s} {d}, and {s} holds {d} element{s}", .{
            lead, at, try typer.comp.typeName(elements.owner), count, plural(count),
        }),
        .label = "past the last element",
    });
}

pub fn checkRangeEnd(typer: *Typer, node: Node.Index) Allocator.Error!?Value {
    const value = try typer.checkValue(node, null);
    const found = typer.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found)) return value;
    try typer.fail(node, .{
        .code = .bad_operand,
        .message = try typer.comp.fmt("an end of a range is a count, and this is {s}", .{
            try typer.comp.typeName(found),
        }),
        .label = "not a count",
        .help = "any integer counts, and nothing else does",
    });
    return null;
}

pub fn rangeIn(typer: *const Typer, view: AST.View.Bracket) ?AST.View.Range {
    if (view.args.len != 1) return null;
    if (typer.tree.nodeTag(view.args[0]) != .range_expr) return null;
    return typer.tree.viewOf(view.args[0]).range_expr;
}

pub fn checkBracketArgs(typer: *Typer, view: AST.View.Bracket) Allocator.Error!void {
    for (view.args) |argument| {
        if (typer.tree.nodeTag(argument) != .range_expr) {
            _ = try typer.checkExpr(argument, null);
            continue;
        }
        const range = typer.tree.viewOf(argument).range_expr;
        _ = try typer.checkExpr(range.start, null);
        if (range.end.unwrap()) |end| _ = try typer.checkExpr(end, null);
    }
}

pub fn checkIndex(typer: *Typer, node: Node.Index, view: AST.View.Bracket) Allocator.Error!?Indexed {
    const comp = typer.comp;
    const elements = try checkElements(typer, node, view) orelse return null;

    if (view.args.len != 1) {
        try checkBracketArgs(typer, view);
        try typer.fail(node, .{
            .code = .wrong_arity,
            .message = try comp.fmt("an index is one value, and this writes {d}", .{
                view.args.len,
            }),
            .label = "the wrong number of values",
            .help = "reach through one step at a time, as in 'grid[1][2]'",
        });
        return null;
    }

    const argument = view.args[0];
    const value = try typer.checkValue(argument, null);
    const found = typer.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found) == false) {
        try typer.fail(argument, .{
            .code = .bad_operand,
            .message = try comp.fmt("an index is a count, and this is {s}", .{
                try comp.typeName(found),
            }),
            .label = "not a count",
            .help = "any integer indexes, and nothing else does",
        });
        return null;
    }
    if (value != .constant) return .{ .elements = elements, .ref = refOf(value), .at = null };

    const written = comp.pool.keyOf(value.constant).value_int.value;
    if (written < 0) {
        try failBeforeFirst(typer, argument, "an index", written);
        return null;
    }
    if (elements.len) |count| {
        if (written >= count) {
            try failPastLast(typer, argument, "this index is", written, elements, count);
            return null;
        }
    }

    var ref = refOf(value);
    if (Pool.isUntyped(found)) {
        const met = try typer.fitValue(value.constant, .u64_type, argument);
        // the value stands inside the length, which a u64 holds by construction
        assert(met == .constant);
        ref = refOf(met);
    }
    return .{ .elements = elements, .ref = ref, .at = @intCast(written) };
}

fn checkElements(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Elements {
    const comp = typer.comp;
    assert(typer.tree.nodeTag(node) == .bracket);

    const base = try Place.checkPlace(typer, view.base) orelse return null;
    const peeled = Expr.peelPointer(&comp.pool, base.type);
    if (peeled.owner == .poison) return null;

    const key = comp.pool.keyOf(peeled.owner);
    const child: Pool.Index, const len: ?u64, const mutable: bool = switch (key) {
        .type_array => |it| .{ it.child, it.len, false },
        .type_slice => |it| .{ it.child, null, it.mutable },
        else => {
            try checkBracketArgs(typer, view);
            try failNotIndexable(typer, node, peeled.owner);
            return null;
        },
    };
    return .{
        .node = node,
        .base = base,
        .pointer = peeled.pointer,
        .owner = peeled.owner,
        .child = child,
        .len = len,
        .mutable = mutable,
    };
}

pub const not_landed_help = "give it a type, as in 'let a: [3]u32 = [1, 2, 3]', and " ++
    "everything it holds can be reached";

fn failNotIndexable(typer: *Typer, node: Node.Index, owner: Pool.Index) Allocator.Error!void {
    @branchHint(.cold);
    const comp = typer.comp;
    if (owner == .untyped_aggregate_type) {
        return typer.fail(node, .{
            .code = .not_indexable,
            .message = "this array has no type yet, so it has no elements to reach",
            .label = "no type in sight",
            .help = not_landed_help,
        });
    }
    try typer.fail(node, .{
        .code = .not_indexable,
        .message = try comp.fmt("{s} cannot be indexed", .{try comp.typeName(owner)}),
        .label = "not something to index",
        .help = "an index reaches an element, and an array is what holds elements",
    });
}

pub fn checkStructLiteral(
    typer: *Typer,
    node: Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = typer.comp;
    const view = typer.tree.viewOf(node).struct_literal;

    const wanted = try structLiteralType(typer, node, view, hint) orelse return .poison;

    const instance = switch (comp.pool.keyOf(wanted)) {
        .type_struct => |instance| instance,
        else => {
            return typer.refuse(view.type_expr.unwrap() orelse node, .{
                .code = .not_a_type,
                .message = try comp.fmt("{s} has no fields to give", .{
                    try comp.typeName(wanted),
                }),
                .label = "not a struct",
            });
        },
    };

    try comp.ensureRows(instance);
    const rows = comp.instanceAt(instance).rows;
    const buildable = try structIsBuildable(typer, node, wanted, instance);
    typer.answerType(node, wanted);

    const start: u32 = @intCast(comp.scratch.operands.items.len);
    defer comp.scratch.operands.shrinkRetainingCapacity(start);
    try comp.scratch.operands.appendNTimes(
        comp.gpa,
        .{ .value = .poison, .initializer = .none },
        rows.len,
    );

    var clean = true;
    for (view.fields) |init_node| {
        if (typer.tree.nodeTag(init_node) != .struct_field_init) continue;
        const field_init = typer.tree.viewOf(init_node).struct_field_init;

        const row: Compilation.Row.Index = row: {
            const name = typer.tree.tokenSlice(field_init.name_token);
            if (try Expr.structMember(typer, instance, name)) |member| {
                if (member == .field) break :row member.field;
            }
            try Expr.reportNoMember(typer, wanted, field_init.name_token, .field);
            _ = try typer.checkExpr(field_init.value, null);
            clean = false;
            continue;
        };
        const position: u32 = row.int() - rows.start;
        typer.linkField(init_node, instance, row);

        if (comp.scratch.operands.items[start + position].initializer.unwrap()) |first| {
            try typer.failToken(field_init.name_token, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is given twice", .{
                    typer.tree.tokenSlice(field_init.name_token),
                }),
                .label = "given again here",
                .notes = try typer.noteHere(first, "first given here"),
            });
            clean = false;
            continue;
        }
        comp.scratch.operands.items[start + position].initializer = init_node.toOptional();

        const row_type = comp.rowAt(.from(rows.at(position))).type;
        const value = try typer.checkExpr(field_init.value, row_type);
        const met = try typer.coerce(value, row_type, field_init.value);
        if (met == .poison) clean = false;
        comp.scratch.operands.items[start + position].value = met;
    }
    if (buildable == false) return .poison;

    var missing: []const u8 = "";
    for (0..rows.len) |position| {
        if (comp.scratch.operands.items[start + position].initializer != .none) continue;
        const name = comp.pool.stringText(comp.rowAt(.from(rows.at(@intCast(position)))).name);
        missing = try quotedList(comp, missing, name);
    }
    if (missing.len > 0) {
        return typer.refuse(node, .{
            .code = .missing_field,
            .message = try comp.fmt("this literal leaves out {s}", .{missing}),
            .label = "incomplete",
            .help = "every field of the struct must be present, and there are no defaults",
        });
    }
    if (clean == false) return .poison;

    return settleAggregate(typer, node, wanted, comp.scratch.operands.items[start..]);
}

fn structLiteralType(
    typer: *Typer,
    node: Node.Index,
    view: AST.View.StructLiteral,
    hint: ?Pool.Index,
) Allocator.Error!?Pool.Index {
    if (view.type_expr.unwrap()) |written| {
        const resolved = try Resolve.resolveType(typer, written);
        return if (resolved == .poison) null else resolved;
    }

    const landing = hint orelse .void_type;
    if (landing == .poison) return null;
    if (landing != .void_type and typer.comp.pool.isUnion(landing) == false) return landing;

    if (landing == .void_type) {
        try typer.fail(node, .{
            .code = .var_needs_type,
            .message = "nothing here says which struct this builds",
            .label = "no type in sight",
            .help = "name it, as in 'Point.{ x: 1 }', or annotate what it feeds",
        });
    } else {
        try typer.fail(node, .{
            .code = .var_needs_type,
            .message = try typer.comp.fmt(
                "this lands on '{s}', which lists several types, and nothing says which is built",
                .{try typer.comp.typeName(landing)},
            ),
            .label = "which member?",
            .help = "name the struct, as in 'Point.{ x: 1 }'",
        });
    }
    return null;
}

fn structIsBuildable(
    typer: *Typer,
    node: Node.Index,
    wanted: Pool.Index,
    instance: Pool.Instance,
) Allocator.Error!bool {
    const comp = typer.comp;
    assert(typer.tree.nodeTag(node) == .struct_literal);
    assert(comp.pool.structOf(wanted) == instance);
    const decl = comp.declAt(comp.instanceDecl(instance));
    if (decl.module == typer.module_index) return true;

    const tree = comp.treeOf(decl.module);
    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        const row = comp.rowAt(.from(raw));
        if (tree.viewOf(row.node).field.is_pub) continue;
        try typer.fail(node, .{
            .code = .private,
            .message = try comp.fmt(
                "{s} keeps '{s}' private to its file, so only that file builds one",
                .{ try comp.typeName(wanted), comp.pool.stringText(row.name) },
            ),
            .label = "private fields",
            .help = "mark every field 'pub', or have that file build it through a function",
            .notes = try comp.noteOne(decl.module, row.node, "declared here"),
        });
        return false;
    }
    return true;
}

fn allConstant(operands: []const Operand) bool {
    for (operands) |operand| if (operand.value != .constant) return false;
    return true;
}

fn settleAggregate(
    typer: *Typer,
    node: Node.Index,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    if (allConstant(operands)) return internAggregate(typer, type_index, operands);
    if (typer.builder == null) {
        return typer.refuse(node, .{
            .code = .not_constant,
            .message = "this must settle before anything runs, and part of this literal does not",
            .label = "not a constant",
        });
    }
    const payload = try typer.emitExtra(&.{@intCast(operands.len)}, operands);
    return typer.emitValue(node, .aggregate_init, type_index, .{ .payload = payload });
}

fn internAggregate(
    typer: *Typer,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    const comp = typer.comp;
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);
    try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, operands.len);
    for (operands) |operand| comp.pool.scratch.appendAssumeCapacity(operand.value.constant);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = type_index,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

pub fn checkArrayLiteral(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const comp = typer.comp;
    const elements = typer.tree.viewOf(node).array_literal;

    const landing: Pool.Index = if (hint) |found|
        aggregateLanding(&comp.pool, found, elements.len)
    else
        .void_type;
    const element_hint: ?Pool.Index = switch (comp.pool.keyOf(landing)) {
        .type_array => |it| it.child,
        .type_slice => |it| it.child,
        else => null,
    };

    const start = comp.scratch.operands.items.len;
    defer comp.scratch.operands.shrinkRetainingCapacity(start);
    try comp.scratch.operands.ensureUnusedCapacity(comp.gpa, elements.len);

    var clean = true;
    var diverged = false;
    for (elements) |element| {
        const value = try typer.checkValue(element, element_hint);
        switch (value) {
            .diverged => diverged = true,
            .poison => clean = false,
            else => comp.scratch.operands.appendAssumeCapacity(.{ .value = value, .initializer = .none }),
        }
    }
    if (diverged) return .diverged;
    if (clean == false) return .poison;
    const operands = comp.scratch.operands.items[start..];

    const storage: Pool.Key.Array = switch (comp.pool.keyOf(landing)) {
        .type_array => |it| it,
        else => |key| {
            if (allConstant(operands)) {
                return internAggregate(typer, .untyped_aggregate_type, operands);
            }
            return typer.refuse(node, if (key == .type_slice) .{
                .code = .not_constant,
                .message = "a view needs bytes the program owns, and part of this " ++
                    "array is settled at run time",
                .label = "not a constant",
                .help = "bind it to storage first and slice that, as in " ++
                    "'var a: [4]u32 = ...' then 'a[0..]'",
            } else .{
                .code = .var_needs_type,
                .message = "nothing says what type this array is",
                .label = "no type in sight",
                .help = "annotate what it feeds, as in 'let a: [2]u32 = ...'",
            });
        },
    };

    if (storage.len != elements.len) {
        return typer.refuse(node, .{
            .code = .does_not_fit,
            .message = try comp.fmt("this literal has {d} element{s}, and {s} holds {d}", .{
                elements.len,
                plural(@intCast(elements.len)),
                try comp.typeName(landing),
                storage.len,
            }),
            .label = "the wrong number of elements",
        });
    }

    for (elements, operands) |element, *operand| {
        operand.value = try typer.coerce(operand.value, storage.child, element);
        if (operand.value == .poison) clean = false;
    }
    if (clean == false) return .poison;
    return settleAggregate(typer, node, landing, operands);
}

fn aggregateLanding(pool: *const Pool, found: Pool.Index, count: usize) Pool.Index {
    if (pool.isUnion(found) == false) return found;
    for (pool.unionMembers(found)) |member| {
        switch (pool.keyOf(member)) {
            .type_array => |array| if (array.len == count) return member,
            .type_slice => return member,
            else => {},
        }
    }
    return found;
}
