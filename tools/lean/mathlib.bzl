"""mathlib_repository: Mathlib's prebuilt .olean files (ADR 0061, section Mathlib).

Lean proofs over reals use Mathlib. Building it from source takes hours, so
this rule clones Mathlib at a pinned commit and runs `lake exe cache get`,
which downloads the .olean files Mathlib's CI built for that commit and
checks their hashes against the sources. Lake reads and fills its own
download cache, `~/.cache/mathlib`, so a machine that keeps it, as CI does,
unpacks them again without downloading.

The repository has the .olean directories of Mathlib and of each package it
depends on under `lib/<package>`, the filegroup `:oleans` of all of them, and
`rev`, the commit, which pia_lean_proof records in each receipt.
"""

def _mathlib_repository_impl(rctx):
    os_name = rctx.os.name.lower()
    arch = rctx.os.arch
    if os_name.startswith("linux") and arch in ["amd64", "x86_64"]:
        toolchain = rctx.attr.lean_linux_x86_64
    elif os_name.startswith("mac") and arch in ["aarch64", "arm64"]:
        toolchain = rctx.attr.lean_macos_arm64
    else:
        fail("Mathlib's prebuilt .olean files are for Linux x86_64 and macOS arm64, not %s %s" % (os_name, arch))
    bin = rctx.path(toolchain).dirname.get_child("bin")
    env = {"PATH": "%s:%s" % (bin, rctx.os.environ.get("PATH", "/usr/bin:/bin"))}

    def run(args, what):
        r = rctx.execute(args, environment = env, timeout = 3600, quiet = False, working_directory = "src")
        if r.return_code != 0:
            fail("mathlib_repository: %s failed:\n%s\n%s" % (what, r.stdout, r.stderr))

    rctx.file("src/.keep", "")
    run(["git", "init", "-q"], "git init")
    run(["git", "fetch", "-q", "--depth=1", rctx.attr.remote, rctx.attr.commit], "fetching Mathlib")
    run(["git", "checkout", "-q", "FETCH_HEAD"], "checking out Mathlib")
    # Lake clones the packages Mathlib's lake-manifest.json pins, then
    # downloads and unpacks the .olean files for this commit.
    run(["lake", "exe", "cache", "get"], "lake exe cache get")

    # Only the .olean directories are kept: Lean finds a module's imports
    # there through LEAN_PATH, and needs nothing else of a package.
    libs = [("Mathlib", "src/.lake/build/lib/lean")]
    packages = rctx.path("src/.lake/packages")
    for p in packages.readdir():
        lib = p.get_child(".lake").get_child("build").get_child("lib").get_child("lean")
        if lib.exists:
            libs.append((p.basename, "src/.lake/packages/%s/.lake/build/lib/lean" % p.basename))
    for name, path in libs:
        r = rctx.execute(["sh", "-c", 'mkdir -p lib && mv "$1" "lib/$2"', "sh", path, name])
        if r.return_code != 0:
            fail("mathlib_repository: cannot move %s: %s" % (path, r.stderr))
    rctx.delete("src")
    rctx.file("rev", rctx.attr.commit + "\n")
    rctx.file("BUILD.bazel", """\
# Mathlib's prebuilt .olean files, written by mathlib_repository.
exports_files(["rev"])

filegroup(
    name = "oleans",
    srcs = glob([
        "lib/**/*.olean",
        "lib/**/*.olean.private",
        "lib/**/*.olean.server",
        "lib/**/*.ir",
        "lib/**/*.ir.sig",
    ]) + ["rev"],
    visibility = ["//visibility:public"],
)
""")

mathlib_repository = repository_rule(
    implementation = _mathlib_repository_impl,
    attrs = {
        "commit": attr.string(mandatory = True, doc = "The Mathlib commit, whose lean-toolchain must be the pinned Lean's."),
        "remote": attr.string(default = "https://github.com/leanprover-community/mathlib4"),
        "lean_linux_x86_64": attr.label(default = "@lean_toolchain_linux_x86_64//:BUILD.bazel"),
        "lean_macos_arm64": attr.label(default = "@lean_toolchain_macos_arm64//:BUILD.bazel"),
    },
    environ = ["PATH", "HOME", "XDG_CACHE_HOME"],
)
