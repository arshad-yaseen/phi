pub const C = @import("C.zig");

test {
    @import("std").testing.refAllDecls(@This());
}
