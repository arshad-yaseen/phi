//! Decodes what a number literal spells, a value, or the refusal to report.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const Diagnostic = @import("../Diagnostic.zig");

pub const Decoded = union(enum) {
    int: i128,
    float: f64,
    refused: Refusal,
};

/// A refusal's words.
pub const Refusal = struct {
    code: Diagnostic.Code,
    message: []const u8,
    label: []const u8,
    help: ?[]const u8 = null,
};

pub fn decode(arena: Allocator, text: []const u8) Allocator.Error!Decoded {
    assert(text.len > 0);

    // most literals are plain decimals, and 18 digits cannot overflow
    if (text.len <= 18) fast: {
        // a leading zero is a prefix or a mistake, so it goes the long way
        if (text.len > 1) {
            if (text[0] == '0') break :fast;
        }
        var value: i128 = 0;
        for (text) |byte| {
            if (byte < '0') break :fast;
            if (byte > '9') break :fast;
            value = value * 10 + (byte - '0');
        }
        return .{ .int = value };
    }
    return decodeSlow(arena, text);
}

fn decodeSlow(arena: Allocator, text: []const u8) Allocator.Error!Decoded {
    switch (std.zig.parseNumberLiteral(text)) {
        .int => |value| return .{ .int = value },
        .big_int => |base| return decodeWide(text, base),
        .float => {
            // `parseNumberLiteral` validated the shape, so the parse cannot fail
            const value = std.fmt.parseFloat(f64, text) catch unreachable;
            if (std.math.isFinite(value) == false) {
                return .{ .refused = .{
                    .code = .bad_number,
                    .message = "this number is too large for a float",
                    .label = "does not fit",
                } };
            }
            return .{ .float = value };
        },
        .failure => |failure| return .{ .refused = try refusalOf(arena, text, failure) },
    }
}

fn decodeWide(text: []const u8, base: std.zig.number_literal.Base) Decoded {
    const radix: u8 = @intFromEnum(base);
    const digits = if (base == .decimal) text else text[2..];

    var value: i128 = 0;
    for (digits) |byte| {
        if (byte == '_') continue;
        // `parseNumberLiteral` validated every digit
        const digit = std.fmt.charToDigit(byte, radix) catch unreachable;
        const wide = std.math.mul(i128, value, radix) catch return too_wide;
        value = std.math.add(i128, wide, digit) catch return too_wide;
    }
    return .{ .int = value };
}

const too_wide: Decoded = .{ .refused = .{
    .code = .bad_number,
    .message = "this number needs more than 128 bits, the width constants fold in",
    .label = "too large",
} };

fn refusalOf(
    arena: Allocator,
    text: []const u8,
    failure: std.zig.number_literal.Error,
) Allocator.Error!Refusal {
    return switch (failure) {
        .leading_zero => .{
            .code = .bad_number,
            .message = "a decimal number cannot start with zero",
            .label = "leading zero",
            .help = "write the '0o' prefix if octal was meant, or drop the zero",
        },
        .digit_after_base => .{
            .code = .bad_number,
            .message = "a base prefix needs digits after it",
            .label = "no digits",
        },
        .upper_case_base => .{
            .code = .bad_number,
            .message = "a base prefix is lowercase: '0x', '0o', or '0b'",
            .label = "uppercase prefix",
        },
        .invalid_float_base => .{
            .code = .bad_number,
            .message = "a float is decimal, or hex with a 'p' exponent",
            .label = "wrong base for a float",
        },
        .repeated_underscore,
        .invalid_underscore_after_special,
        .trailing_underscore,
        .exponent_after_underscore,
        .special_after_underscore,
        => .{
            .code = .bad_number,
            .message = "'_' separates digits, so one sits between two of them",
            .label = "misplaced '_'",
        },
        .invalid_digit => |info| .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(arena, "'{c}' is not a {t} digit", .{
                text[info.i], info.base,
            }),
            .label = "not a digit",
        },
        .invalid_digit_exponent => |at| .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(arena, "'{c}' is not a digit an exponent takes", .{
                text[at],
            }),
            .label = "not an exponent digit",
        },
        .duplicate_period => .{
            .code = .bad_number,
            .message = "a number holds one '.'",
            .label = "a second '.'",
        },
        .duplicate_exponent => .{
            .code = .bad_number,
            .message = "a number holds one exponent",
            .label = "a second exponent",
        },
        .trailing_special => .{
            .code = .bad_number,
            .message = "this number ends before its digits do",
            .label = "digits expected after this",
        },
        .invalid_exponent_sign => |at| .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(
                arena,
                "a sign continues an exponent, and '{c}' follows a digit",
                .{text[at]},
            ),
            .label = "misplaced sign",
        },
        .period_after_exponent => .{
            .code = .bad_number,
            .message = "an exponent holds no '.'",
            .label = "'.' in an exponent",
        },
        .invalid_character => .{
            .code = .bad_number,
            .message = try std.fmt.allocPrint(arena, "'{s}' is not a number the language knows", .{
                text,
            }),
            .label = "unreadable",
            .help = "numbers are decimal, hex '0x', octal '0o', or binary '0b', " ++
                "with '.' and 'e' for floats",
        },
    };
}

const testing = std.testing;

test "every base folds, wide values included" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    try testing.expectEqual(@as(i128, 0), (try decode(arena, "0")).int);
    try testing.expectEqual(@as(i128, 1_000_000), (try decode(arena, "1_000_000")).int);
    try testing.expectEqual(@as(i128, 255), (try decode(arena, "0xff")).int);
    try testing.expectEqual(@as(i128, 10), (try decode(arena, "0b1010")).int);
    try testing.expectEqual(@as(i128, 1) << 64, (try decode(arena, "18446744073709551616")).int);
    try testing.expectEqual(@as(f64, 3.0), (try decode(arena, "0x1.8p1")).float);
    try testing.expectEqual(@as(f64, 0.25), (try decode(arena, "2.5e-1")).float);
}

test "every malformed shape is refused, the edges by their width" {
    var arena_state: std.heap.ArenaAllocator = .init(testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const wide = try decode(arena, "170141183460469231731687303715884105728");
    try testing.expectEqual(Diagnostic.Code.bad_number, wide.refused.code);
    try testing.expectEqual(Diagnostic.Code.bad_number, (try decode(arena, "1e999")).refused.code);
    try testing.expectEqual(Diagnostic.Code.bad_number, (try decode(arena, "09")).refused.code);
    try testing.expectEqual(Diagnostic.Code.bad_number, (try decode(arena, "1__0")).refused.code);
    try testing.expectEqual(Diagnostic.Code.bad_number, (try decode(arena, "0X1")).refused.code);
    try testing.expectEqual(Diagnostic.Code.bad_number, (try decode(arena, "1$")).refused.code);
}
