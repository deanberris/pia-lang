"""Bazel rules for compiling Pia programs with piac."""

load("@rules_cc//cc:defs.bzl", "cc_binary")
load(":targets.bzl", "PIAC_TARGET_FLAGS")

def pia_object(
        name,
        src,
        allow_unproved = [],
        solver_rlimit = 1200000000,
        solver_timeout_ms = 600000,
        **kwargs):
    """Proves a Pia file and compiles it to an object file, `<name>.o`, for
    the platform being built for (tools/piac/targets.bzl).

    piac refuses to compile a program with a failed or unproved goal, so the
    build fails unless every goal is proved, or accepted by one of
    `allow_unproved` (each passed as `--allow-unproved=<spec>`).

    Each obligation gets `solver_rlimit` units of Z3's deterministic resource
    limit (`--solver-rlimit`). The rlimit, not the wall clock, decides whether
    a goal is proved, so the result does not depend on how loaded the machine
    is. The default is about 20 times the costliest goal in the repository,
    as measured by `piac --solver-cost` (docs/verifier.md, "Timeouts").

    `solver_timeout_ms` is only a last-resort safety net against a query
    that runs for a long time without spending its rlimit; it should never
    be what decides a goal.

    Put the result in the `srcs` of a cc_library or cc_binary to call the
    program's functions from C (docs/codegen.md, "C ABI").
    """
    flags = " ".join(["--allow-unproved=" + spec for spec in allow_unproved] +
                     ["--solver-rlimit=%d" % solver_rlimit,
                      "--solver-timeout=%d" % solver_timeout_ms])
    native.genrule(
        name = name,
        srcs = [src],
        outs = [name + ".o"],
        cmd = "$(location //tools/piac) --emit=obj %s " % flags + PIAC_TARGET_FLAGS + " -o $@ $<",
        tools = ["//tools/piac"],
        **kwargs
    )

def _target_args(ctx):
    """piac's --target and --cpu for the platform being built for, as in
    PIAC_TARGET_FLAGS (a rule cannot read a select from a .bzl constant)."""
    linux = ctx.attr._linux[platform_common.ConstraintValueInfo]
    x86_64 = ctx.attr._x86_64[platform_common.ConstraintValueInfo]
    if ctx.target_platform_has_constraint(linux) and ctx.target_platform_has_constraint(x86_64):
        return ["--target=x86_64-unknown-linux-gnu", "--cpu=x86-64-v3"]
    return ["--target=arm64-apple-macosx14.0.0", "--cpu=apple-m1"]

PiaInfo = provider(
    doc = "A Pia module built by pia_library (ADR 0039).",
    fields = {
        "interfaces": "The directory of the module's `.piai` interface artifacts.",
        "objects": "A depset of the object files of the module and of every module it imports.",
    },
)

def _pia_library_impl(ctx):
    src = ctx.file.src
    piac = ctx.executable._piac

    # The interfaces need only the source, so importers can start on them
    # while this module is still being proved.
    interfaces = ctx.actions.declare_directory(ctx.label.name + ".piai")
    ctx.actions.run(
        executable = piac,
        arguments = ["--emit=interface", "-o", interfaces.path, src.path],
        inputs = [src],
        outputs = [interfaces],
        mnemonic = "PiaInterface",
        progress_message = "Writing the interfaces of %s" % src.short_path,
    )

    # Strict dependencies: a module sees the interfaces of the modules it
    # declares, never those they import in turn, nor any object file.
    imported = [dep[PiaInfo].interfaces for dep in ctx.attr.deps]
    obj = ctx.actions.declare_file(ctx.label.name + ".o")
    args = ["--emit=obj", "-o", obj.path] + _target_args(ctx)
    args += ["--iface-path=" + d.path for d in imported]
    args += ["--allow-unproved=" + spec for spec in ctx.attr.allow_unproved]
    args += [
        "--solver-rlimit=%d" % ctx.attr.solver_rlimit,
        "--solver-timeout=%d" % ctx.attr.solver_timeout_ms,
        src.path,
    ]
    ctx.actions.run(
        executable = piac,
        arguments = args,
        inputs = [src] + imported,
        outputs = [obj],
        mnemonic = "PiaCompile",
        progress_message = "Proving and compiling %s" % src.short_path,
    )
    objects = depset([obj], transitive = [dep[PiaInfo].objects for dep in ctx.attr.deps])

    # The link check (docs/abi.md): every interface an object of this
    # module's closure was proved against is provided by another, with the
    # same hash. A validation action, so it runs whenever this target builds
    # but nothing waits for it.
    checked = ctx.actions.declare_file(ctx.label.name + ".cert-check")
    ctx.actions.run(
        executable = ctx.executable._pia_cert,
        arguments = ["check", "--stamp=" + checked.path] + [o.path for o in objects.to_list()],
        inputs = objects,
        outputs = [checked],
        mnemonic = "PiaCertCheck",
        progress_message = "Checking the certificates of %s" % src.short_path,
    )
    return [
        DefaultInfo(files = objects),
        PiaInfo(interfaces = interfaces, objects = objects),
        OutputGroupInfo(
            interfaces = depset([interfaces]),
            _validation = depset([checked]),
        ),
    ]

pia_library = rule(
    implementation = _pia_library_impl,
    doc = """Proves and compiles one Pia module, a file with a `module` header.

Its outputs are the object files of the module and of the modules it
imports, so a cc_library, cc_binary or cc_test can list it in `srcs` to call
its C entry points (docs/codegen.md, "C ABI").

Importers depend only on its interface artifacts, `<name>.piai/`, which
`piac --emit=interface` writes from the source alone. A change that leaves
them byte-identical (a private item, a body, a comment) does not rebuild any
importer. Each `import M.I` must be provided by a module in `deps`: the
interfaces of modules further down are not visible (ADR 0039).

`allow_unproved`, `solver_rlimit` and `solver_timeout_ms` are as for
pia_object.
""",
    attrs = {
        "src": attr.label(allow_single_file = [".pia", ".pia.md"], mandatory = True),
        "deps": attr.label_list(providers = [PiaInfo]),
        "allow_unproved": attr.string_list(),
        "solver_rlimit": attr.int(default = 1200000000),
        "solver_timeout_ms": attr.int(default = 600000),
        "_linux": attr.label(default = "@platforms//os:linux"),
        "_x86_64": attr.label(default = "@platforms//cpu:x86_64"),
        "_piac": attr.label(
            default = "//tools/piac",
            executable = True,
            cfg = "exec",
        ),
        "_pia_cert": attr.label(
            default = "//tools/pia-cert",
            executable = True,
            cfg = "exec",
        ),
    },
)

def pia_binary(name, src, deps = [], **kwargs):
    """A program whose `main` is in the Pia file `src`, which may import `deps`.

    It is the module `<name>_main`, built by pia_library, linked as a
    cc_binary. Other keyword arguments go to the cc_binary.
    """
    pia_library(
        name = name + "_main",
        src = src,
        deps = deps,
        target_compatible_with = kwargs.get("target_compatible_with", []),
    )
    cc_binary(
        name = name,
        srcs = [":" + name + "_main"],
        **kwargs
    )
