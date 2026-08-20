pub const AST = @import("AST.zig");
pub const Compilation = @import("Compilation.zig");
pub const Diagnostic = @import("Diagnostic.zig");
pub const Source = @import("Source.zig");
pub const Spell = @import("Spell.zig");
pub const Target = @import("Target.zig").Target;
pub const codegen = struct {
    pub const C = @import("codegen/C.zig");
};

test {
    @import("std").testing.refAllDecls(@This());
}
