const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Check = @import("../Check.zig");
const Compilation = @import("../Compilation.zig");
const IR = @import("../IR.zig");
const Pool = @import("../Pool.zig");
const Resolve = @import("Resolve.zig");
const Expr = @import("Expr.zig");
const Call = @import("Call.zig");
const Place = @import("Place.zig");

const Node = AST.Node;
const Ref = IR.Ref;
const Value = Check.Value;
const Operand = Check.Operand;
const refOf = Check.refOf;
const runtimeValue = Check.runtimeValue;
const plural = Check.plural;
const quotedList = Check.quotedList;

pub fn elementExample(check: *Check, aggregate: Pool.Key.Aggregate) Allocator.Error![]const u8 {
    if (aggregate.elems.len == 0) return "u32";
    const found = check.comp.pool.typeOfValue(aggregate.elems[0]);
    if (Pool.isUntyped(found)) return "u32";
    return check.comp.typeName(found);
}

const range_help = "the ends of a range take each other's type, and nothing converts on its own";

pub fn checkBracketExpr(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    if (Call.baseIsNamespace(check, view.base) == false) return checkIndexExpr(check, node, view);

    const base = try check.checkExpr(view.base, null);
    switch (base) {
        .named_generic => {
            const resolved = try Resolve.resolveBracketType(check, node);
            if (resolved == .poison) return .poison;
            return .{ .named_type = resolved };
        },
        .named_fn => {
            return check.refuse(node, .{
                .code = .not_a_function,
                .message = "a function with its type arguments is still not a value, so call it",
                .label = "missing the call",
            });
        },
        .diverged => return .diverged,
        .poison => return .poison,
        .constant, .runtime => return checkIndexExpr(check, node, view),
        else => {
            return check.refuse(node, .{
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
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    const comp = check.comp;
    if (rangeIn(check, view)) |range| return checkSlice(check, node, view, range);

    const indexed = try checkIndex(check, node, view) orelse return .poison;
    if (indexed.at) |at| {
        if (indexed.elements.pointer == null) {
            if (Place.placeConstant(check, indexed.elements.base)) |aggregate| {
                return .{ .constant = comp.pool.aggregateAt(aggregate, at) };
            }
        }
    }

    assert(check.builder != null);
    const place = try Place.elementPlace(check, indexed.elements, indexed.ref) orelse return .poison;
    return runtimeValue(try Place.placeValue(check, place), place.type);
}

fn checkSlice(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
    range: AST.View.Range,
) Allocator.Error!Value {
    if (check.builder == null) return check.needRuntime(node, "making a view");

    const elements = try checkElements(check, node, view) orelse return .poison;
    const through = try Place.elementsThrough(check, elements) orelse return .poison;
    const bounds = try checkRange(check, view.args[0], range, elements, through) orelse
        return .poison;

    if (Place.refIsConstant(bounds.start) == false or Place.refIsConstant(bounds.end) == false) {
        try Place.emitCheck(check, elements.node, .order_check, bounds.start, bounds.end);
    }
    if (range.end != .none and Place.settledAgainstBase(elements, bounds.end) == false) {
        const length = try Place.baseLengthRef(check, elements, through);
        try Place.emitCheck(check, elements.node, .order_check, bounds.end, length);
    }

    const made = try check.sliceOf(elements.child, through.mutable());
    const payload = try check.emitExtra(&.{
        @intFromEnum(through.ref),
        @intFromEnum(bounds.start),
        @intFromEnum(bounds.end),
    }, &.{});
    return check.emitValue(node, .slice_make, made, .{ .payload = payload });
}

const Bounds = struct { start: Ref, end: Ref };

fn checkRange(
    check: *Check,
    range_node: Node.Index,
    range: AST.View.Range,
    elements: Elements,
    through: Place,
) Allocator.Error!?Bounds {
    const start = try checkRangeEnd(check, range.start) orelse return null;
    const end_node = range.end.unwrap() orelse range_node;
    const end = if (range.end != .none)
        try checkRangeEnd(check, end_node) orelse return null
    else if (elements.len) |count|
        try check.untypedInt(count)
    else
        try check.emitOneValue(elements.node, .slice_len, .u64_type, through.ref);

    const ends = try settleEnds(
        check,
        range_node,
        .{ .value = start, .node = range.start },
        .{ .value = end, .node = end_node },
    ) orelse return null;

    if (countOf(check, ends.start)) |at| {
        if (at < 0) {
            try failBeforeFirst(check, range.start, "an end of a range", at);
            return null;
        }
    }
    if (countOf(check, ends.end)) |at| {
        if (at < 0) {
            try failBeforeFirst(check, end_node, "an end of a range", at);
            return null;
        }
    }
    if (try rangeRunsBackwards(check, range_node, ends.start, ends.end)) return null;
    if (countOf(check, ends.end)) |at| {
        if (elements.len) |count| {
            if (at > count) {
                try failPastLast(check, end_node, "this range ends at", at, elements, count);
                return null;
            }
        }
    }
    return .{ .start = refOf(ends.start), .end = refOf(ends.end) };
}

const End = struct { value: Value, node: Node.Index };

const Ends = struct { start: Value, end: Value, type: Pool.Index };

pub fn settleEnds(check: *Check, range_node: Node.Index, start: End, end: End) Allocator.Error!?Ends {
    const left = check.typeOf(start.value);
    const right = check.typeOf(end.value);
    if (Pool.isUntyped(left) == false and Pool.isUntyped(right) == false and left != right) {
        try Expr.failMixedTypes(check, check.tree.nodeMainToken(range_node), left, right, range_help);
        return null;
    }

    var settled = left;
    if (Pool.isUntyped(settled)) settled = right;
    if (Pool.isUntyped(settled)) settled = .u64_type;

    const first = try check.coerce(start.value, settled, start.node);
    const second = try check.coerce(end.value, settled, end.node);
    if (first == .poison or second == .poison) return null;
    return .{ .start = first, .end = second, .type = settled };
}

pub fn rangeRunsBackwards(
    check: *Check,
    range_node: Node.Index,
    start: Value,
    end: Value,
) Allocator.Error!bool {
    const low = countOf(check, start) orelse return false;
    const high = countOf(check, end) orelse return false;
    if (low <= high) return false;

    try check.failToken(check.tree.nodeMainToken(range_node), .{
        .code = .out_of_range,
        .message = try check.comp.fmt(
            "this range starts at {d} and ends at {d}, so it runs backwards",
            .{ low, high },
        ),
        .label = "the ends cross",
        .help = "a range runs from its start up to, but not including, its end",
    });
    return true;
}

fn countOf(check: *const Check, value: Value) ?i128 {
    if (value != .constant) return null;
    return switch (check.comp.pool.keyOf(value.constant)) {
        .value_int => |it| it.value,
        else => null,
    };
}

fn failBeforeFirst(
    check: *Check,
    node: Node.Index,
    what: []const u8,
    at: i128,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .out_of_range,
        .message = try check.comp.fmt("{s} counts from zero, and this one is {d}", .{ what, at }),
        .label = "before the first element",
    });
}

fn failPastLast(
    check: *Check,
    node: Node.Index,
    lead: []const u8,
    at: i128,
    elements: Elements,
    count: u64,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .out_of_range,
        .message = try check.comp.fmt("{s} {d}, and {s} holds {d} element{s}", .{
            lead, at, try check.comp.typeName(elements.owner), count, plural(count),
        }),
        .label = "past the last element",
    });
}

pub fn checkRangeEnd(check: *Check, node: Node.Index) Allocator.Error!?Value {
    const value = try check.checkValue(node, null);
    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found)) return value;
    try check.fail(node, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("an end of a range is a count, and this is {s}", .{
            try check.comp.typeName(found),
        }),
        .label = "not a count",
        .help = "any integer counts, and nothing else does",
    });
    return null;
}

pub fn rangeIn(check: *const Check, view: AST.View.Bracket) ?AST.View.Range {
    if (view.args.len != 1) return null;
    if (check.tree.nodeTag(view.args[0]) != .range_expr) return null;
    return check.tree.viewOf(view.args[0]).range_expr;
}

pub fn checkBracketArgs(check: *Check, view: AST.View.Bracket) Allocator.Error!void {
    for (view.args) |argument| {
        if (check.tree.nodeTag(argument) != .range_expr) {
            _ = try check.checkExpr(argument, null);
            continue;
        }
        const range = check.tree.viewOf(argument).range_expr;
        _ = try check.checkExpr(range.start, null);
        if (range.end.unwrap()) |end| _ = try check.checkExpr(end, null);
    }
}

pub fn checkIndex(check: *Check, node: Node.Index, view: AST.View.Bracket) Allocator.Error!?Indexed {
    const comp = check.comp;
    const elements = try checkElements(check, node, view) orelse return null;

    if (view.args.len != 1) {
        try checkBracketArgs(check, view);
        try check.fail(node, .{
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
    const value = try check.checkValue(argument, null);
    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found) == false) {
        try check.fail(argument, .{
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
        try failBeforeFirst(check, argument, "an index", written);
        return null;
    }
    if (elements.len) |count| {
        if (written >= count) {
            try failPastLast(check, argument, "this index is", written, elements, count);
            return null;
        }
    }

    var ref = refOf(value);
    if (Pool.isUntyped(found)) {
        const met = try check.fitValue(value.constant, .u64_type, argument);
        // the value stands inside the length, which a u64 holds by construction
        assert(met == .constant);
        ref = refOf(met);
    }
    return .{ .elements = elements, .ref = ref, .at = @intCast(written) };
}

fn checkElements(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Elements {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .bracket);

    const base = try Place.checkPlace(check, view.base) orelse return null;
    const peeled = Expr.peelPointer(&comp.pool, base.type);
    if (peeled.owner == .poison) return null;

    const key = comp.pool.keyOf(peeled.owner);
    const child: Pool.Index, const len: ?u64, const mutable: bool = switch (key) {
        .type_array => |it| .{ it.child, it.len, false },
        .type_slice => |it| .{ it.child, null, it.mutable },
        else => {
            try checkBracketArgs(check, view);
            try failNotIndexable(check, node, peeled.owner);
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

fn failNotIndexable(check: *Check, node: Node.Index, owner: Pool.Index) Allocator.Error!void {
    @branchHint(.cold);
    const comp = check.comp;
    if (owner == .untyped_aggregate_type) {
        return check.fail(node, .{
            .code = .not_indexable,
            .message = "this array has no type yet, so it has no elements to reach",
            .label = "no type in sight",
            .help = not_landed_help,
        });
    }
    try check.fail(node, .{
        .code = .not_indexable,
        .message = try comp.fmt("{s} cannot be indexed", .{try comp.typeName(owner)}),
        .label = "not something to index",
        .help = "an index reaches an element, and an array is what holds elements",
    });
}

pub fn checkStructLiteral(
    check: *Check,
    node: Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const view = check.tree.viewOf(node).struct_literal;

    const wanted = try structLiteralType(check, node, view, hint) orelse return .poison;

    const instance = switch (comp.pool.keyOf(wanted)) {
        .type_struct => |instance| instance,
        else => {
            return check.refuse(view.type_expr.unwrap() orelse node, .{
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
    const buildable = try structIsBuildable(check, node, wanted, instance);

    const start: u32 = @intCast(comp.scratch.operands.items.len);
    defer comp.scratch.operands.shrinkRetainingCapacity(start);
    try comp.scratch.operands.appendNTimes(
        comp.gpa,
        .{ .value = .poison, .initializer = .none },
        rows.len,
    );

    var clean = true;
    for (view.fields) |init_node| {
        if (check.tree.nodeTag(init_node) != .struct_field_init) continue;
        const field_init = check.tree.viewOf(init_node).struct_field_init;

        const row: Compilation.Row.Index = row: {
            const name = check.tree.tokenSlice(field_init.name_token);
            if (try Expr.structMember(check, instance, name)) |member| {
                if (member == .field) break :row member.field;
            }
            try Expr.reportNoMember(check, wanted, field_init.name_token, .field);
            _ = try check.checkExpr(field_init.value, null);
            clean = false;
            continue;
        };
        const position: u32 = row.int() - rows.start;

        if (comp.scratch.operands.items[start + position].initializer.unwrap()) |first| {
            try check.failToken(field_init.name_token, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is given twice", .{
                    check.tree.tokenSlice(field_init.name_token),
                }),
                .label = "given again here",
                .notes = try check.noteHere(first, "first given here"),
            });
            clean = false;
            continue;
        }
        comp.scratch.operands.items[start + position].initializer = init_node.toOptional();

        const row_type = comp.rowAt(.from(rows.at(position))).type;
        const value = try check.checkExpr(field_init.value, row_type);
        const met = try check.coerce(value, row_type, field_init.value);
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
        return check.refuse(node, .{
            .code = .missing_field,
            .message = try comp.fmt("this literal leaves out {s}", .{missing}),
            .label = "incomplete",
            .help = "every field of the struct must be present, and there are no defaults",
        });
    }
    if (clean == false) return .poison;

    return settleAggregate(check, node, wanted, comp.scratch.operands.items[start..]);
}

fn structLiteralType(
    check: *Check,
    node: Node.Index,
    view: AST.View.StructLiteral,
    hint: ?Pool.Index,
) Allocator.Error!?Pool.Index {
    if (view.type_expr.unwrap()) |written| {
        const resolved = try Resolve.resolveType(check, written);
        return if (resolved == .poison) null else resolved;
    }

    const landing = hint orelse .void_type;
    if (landing == .poison) return null;
    if (landing != .void_type and check.comp.pool.isUnion(landing) == false) return landing;

    if (landing == .void_type) {
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = "nothing here says which struct this builds",
            .label = "no type in sight",
            .help = "name it, as in 'Point.{ x: 1 }', or annotate what it feeds",
        });
    } else {
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = try check.comp.fmt(
                "this lands on '{s}', which lists several types, and nothing says which is built",
                .{try check.comp.typeName(landing)},
            ),
            .label = "which member?",
            .help = "name the struct, as in 'Point.{ x: 1 }'",
        });
    }
    return null;
}

fn structIsBuildable(
    check: *Check,
    node: Node.Index,
    wanted: Pool.Index,
    instance: Pool.Instance,
) Allocator.Error!bool {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .struct_literal);
    assert(comp.pool.structOf(wanted) == instance);
    const decl = comp.declAt(comp.instanceDecl(instance));
    if (decl.module == check.module_index) return true;

    const tree = comp.treeOf(decl.module);
    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        const row = comp.rowAt(.from(raw));
        if (tree.viewOf(row.node).field.is_pub) continue;
        try check.fail(node, .{
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
    check: *Check,
    node: Node.Index,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    if (allConstant(operands)) return internAggregate(check, type_index, operands);
    if (check.builder == null) {
        return check.refuse(node, .{
            .code = .not_constant,
            .message = "this must settle before anything runs, and part of this literal does not",
            .label = "not a constant",
        });
    }
    const payload = try check.emitExtra(&.{@intCast(operands.len)}, operands);
    return check.emitValue(node, .aggregate_init, type_index, .{ .payload = payload });
}

fn internAggregate(
    check: *Check,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    const comp = check.comp;
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);
    try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, operands.len);
    for (operands) |operand| comp.pool.scratch.appendAssumeCapacity(operand.value.constant);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = type_index,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

pub fn checkArrayLiteral(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const comp = check.comp;
    const elements = check.tree.viewOf(node).array_literal;

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
        const value = try check.checkValue(element, element_hint);
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
                return internAggregate(check, .untyped_aggregate_type, operands);
            }
            return check.refuse(node, if (key == .type_slice) .{
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
        return check.refuse(node, .{
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
        operand.value = try check.coerce(operand.value, storage.child, element);
        if (operand.value == .poison) clean = false;
    }
    if (clean == false) return .poison;
    return settleAggregate(check, node, landing, operands);
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
