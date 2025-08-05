const std = @import("std");

pub fn build(b: *std.Build) void {
    // Common CLI flags: -Dtarget=…  -Doptimize=…
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    //----------------------------------------------------------------------
    // Helper/library modules (same on every Zig version)
    //----------------------------------------------------------------------
    const mod_vm = b.addModule("vm", .{ .root_source_file = b.path("src/vm.zig") });
    const mod_ir = b.addModule("ir", .{ .root_source_file = b.path("src/ir.zig") });
    const mod_memory = b.addModule("memory", .{ .root_source_file = b.path("src/memory.zig") });
    const mod_function = b.addModule("function", .{ .root_source_file = b.path("src/function.zig") });
    const mod_layered_map = b.addModule("layered_map", .{ .root_source_file = b.path("src/layered_map.zig") });

    //----------------------------------------------------------------------
    // Executable — handle the “old” and “new” build-API variants
    //----------------------------------------------------------------------
    const EO = std.Build.ExecutableOptions;
    var exe: *std.Build.Step.Compile = undefined;

    if (@hasField(EO, "root_source_file")) {
        //------------------------------------------------------------------
        // **Stable <= 0.14.x** path
        //------------------------------------------------------------------
        exe = b.addExecutable(.{
            .name = "napalm",
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        });
    } else {
        //------------------------------------------------------------------
        // **Nightly >= 0.15-dev** path
        //------------------------------------------------------------------
        const main_mod = b.addModule("root", .{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        });

        exe = b.addExecutable(.{
            .name = "napalm",
            .root_module = main_mod,
        });
    }

    // ----- make helper modules visible *inside* vm -----
    mod_vm.addImport("memory", mod_memory);
    mod_vm.addImport("ir", mod_ir);
    mod_vm.addImport("function", mod_function);
    mod_vm.addImport("layered_map", mod_layered_map);

    //----------------------------------------------------------------------
    // Wire the helper modules into the executable’s root module
    //----------------------------------------------------------------------
    exe.root_module.addImport("vm", mod_vm);
    exe.root_module.addImport("ir", mod_ir);
    exe.root_module.addImport("memory", mod_memory);
    exe.root_module.addImport("function", mod_function);
    exe.root_module.addImport("layered_map", mod_layered_map);

    // Optional: enable ASan while hunting segfaults
    // exe.root_module.sanitize = .address;

    b.installArtifact(exe);

    //----------------------------------------------------------------------
    // Convenience: `zig build run -- <args>`
    //----------------------------------------------------------------------
    const run_cmd = b.addRunArtifact(exe);
    if (b.args) |args| run_cmd.addArgs(args);
    b.step("run", "Run the Napalm executable").dependOn(&run_cmd.step);
}
