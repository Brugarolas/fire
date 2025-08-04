const std = @import("std");

pub fn build(b: *std.Build) void {
    // Standard target/optimization flags
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Feature toggles
    const opt_trace = b.option(bool, "trace", "Enable VM tracing/log hooks") orelse false;

    // Build-time options reachable via @import("build_options")
    const build_opts = b.addOptions();
    build_opts.addOption(bool, "trace", opt_trace);

    // ---- Modules (Zig 0.14 API) --------------------------------------------
    //const mod_token  = b.addModule("token",  .{ .root_source_file = b.path("src/token.zig") });
    //const mod_parser = b.addModule("parser", .{ .root_source_file = b.path("src/parser.zig") });
    const mod_vm = b.addModule("vm", .{ .root_source_file = b.path("src/vm.zig") });
    const mod_ir = b.addModule("ir", .{ .root_source_file = b.path("src/ir.zig") });
    const mod_memory = b.addModule("memory", .{ .root_source_file = b.path("src/memory.zig") });
    const mod_function = b.addModule("function", .{ .root_source_file = b.path("src/function.zig") });
    const mod_layered_map = b.addModule("layered_map", .{ .root_source_file = b.path("src/layered_map.zig") });

    mod_vm.addImport("ir", mod_ir);
    mod_vm.addImport("memory", mod_memory);
    mod_vm.addImport("function", mod_function);
    mod_vm.addImport("layered_map", mod_layered_map);

    // ---- Executable ---------------------------------------------------------
    const exe = b.addExecutable(.{
        .name = "napalm",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    //exe.root_module.addImport("token",  mod_token);
    //exe.root_module.addImport("parser", mod_parser);
    exe.root_module.addImport("vm", mod_vm);
    exe.root_module.addImport("ir", mod_ir);
    exe.root_module.addImport("memory", mod_memory);
    exe.root_module.addImport("function", mod_function);
    exe.root_module.addImport("layered_map", mod_layered_map);
    //exe.root_module.addOptions("build_options", build_opts);

    b.installArtifact(exe);

    // zig build run -- <args>
    const run_cmd = b.addRunArtifact(exe);
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run the Napalm executable");
    run_step.dependOn(&run_cmd.step);

    // ---- Static library (for embedding) ------------------------------------
    const lib = b.addStaticLibrary(.{
        .name = "napalm",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    //lib.root_module.addImport("token",  mod_token);
    //lib.root_module.addImport("parser", mod_parser);
    lib.root_module.addImport("vm", mod_vm);
    lib.root_module.addImport("ir", mod_ir);
    lib.root_module.addImport("memory", mod_memory);
    lib.root_module.addImport("function", mod_function);
    lib.root_module.addImport("layered_map", mod_layered_map);
    //lib.root_module.addOptions("build_options", build_opts);

    b.installArtifact(lib);

    // ---- Tests --------------------------------------------------------------
    const unit_tests = b.addTest(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    //unit_tests.root_module.addImport("token",  mod_token);
    //unit_tests.root_module.addImport("parser", mod_parser);
    unit_tests.root_module.addImport("ir", mod_ir);
    unit_tests.root_module.addImport("memory", mod_memory);
    unit_tests.root_module.addImport("vm", mod_vm);
    unit_tests.root_module.addImport("function", mod_function);
    unit_tests.root_module.addImport("layered_map", mod_layered_map);
    //unit_tests.root_module.addOptions("build_options", build_opts);

    const test_run = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&test_run.step);

    // Quick compile check (no run)
    const check_step = b.step("check", "Build (no run) to validate it compiles");
    check_step.dependOn(&exe.step);
}
