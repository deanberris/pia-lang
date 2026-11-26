"""Metal libraries built at build time (ADR 0068, ADR 0070).

metal_library compiles one Metal Shading Language file with Xcode's Metal
toolchain (xcrun metal, then metallib), with fast math off, producing
`<name>.metallib`. Pia targets embed it directly via `embeds = [":<name>"]`
and `@embed(file = "<name>.metallib")` (ADR 0070). It runs only on macOS,
with Xcode and its Metal toolchain installed
(`xcodebuild -downloadComponent MetalToolchain`).
"""

def metal_library(name, src, **kwargs):
    """Builds `<name>.metallib` from the Metal Shading Language file `src`."""
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
