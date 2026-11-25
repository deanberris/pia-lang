"""Metal libraries built at build time (ADR 0068, section 2, step 5).

metal_library compiles one Metal Shading Language file with Xcode's Metal
toolchain (xcrun metal, then metallib), with fast math off, and embeds the
.metallib in a cc_library as the bytes `<symbol>` and their length
`<symbol>_len`. It runs only on macOS, with Xcode and its Metal toolchain
installed (`xcodebuild -downloadComponent MetalToolchain`).
"""

load("@rules_cc//cc:defs.bzl", "cc_library")

def metal_library(name, src, symbol, **kwargs):
    """A .metallib from `src`, and `name` + "_embed", a cc_library holding it."""
    tags = ["no-sandbox", "requires-darwin", "requires-metal"] + kwargs.pop("tags", [])
    compat = kwargs.pop("target_compatible_with", ["@platforms//os:macos"])
    native.genrule(
        name = name + "_air",
        srcs = [src],
        outs = [name + ".air"],
        cmd = "xcrun -sdk macosx metal -fno-fast-math -c $< -o $@",
        tags = tags,
        target_compatible_with = compat,
    )
    native.genrule(
        name = name,
        srcs = [":" + name + "_air"],
        outs = [name + ".metallib"],
        cmd = "xcrun -sdk macosx metallib $< -o $@",
        tags = tags,
        target_compatible_with = compat,
        **kwargs
    )
    native.genrule(
        name = name + "_c",
        srcs = [":" + name],
        outs = [name + "_embed.c"],
        tags = tags,
        cmd = ("(echo 'const unsigned char %s[] = {'; " +
               "xxd -i < $<; echo '};'; " +
               "echo 'const unsigned long %s_len = sizeof %s;') > $@") % (symbol, symbol, symbol),
        target_compatible_with = compat,
    )
    cc_library(
        name = name + "_embed",
        srcs = [":" + name + "_c"],
        tags = tags,
        target_compatible_with = compat,
    )
