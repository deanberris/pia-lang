"""The platforms Pia compiles for, and how Bazel tells piac which one (ADR 0049).

| Platform        | Triple                      | CPU         |
|-----------------|-----------------------------|-------------|
| macOS, arm64    | `arm64-apple-macosx14.0.0`  | `apple-m1`  |
| Linux, x86_64   | `x86_64-unknown-linux-gnu`  | `x86-64-v3` |

Objects are always compiled for the platform Bazel builds for, never for
piac's own host, so a cross build only needs `--platforms`.
"""

# `target_compatible_with` for anything that runs piac's output, or needs a
# target piac can compile for. Other platforms skip it.
PIA_TARGETS = select({
    "//tools/piac:macos_arm64": [],
    "//tools/piac:linux_x86_64": [],
    "//conditions:default": ["@platforms//:incompatible"],
})

# `target_compatible_with` for what only runs on Apple silicon, such as a
# demo that reads images with ImageIO.
APPLE_SILICON = [
    "@platforms//os:macos",
    "@platforms//cpu:arm64",
]

# piac's code generation flags for the platform being built for, for a
# genrule's `cmd`: `"$(location //tools/piac) --emit=obj " + PIAC_TARGET_FLAGS`.
PIAC_TARGET_FLAGS = select({
    "//tools/piac:linux_x86_64": "--target=x86_64-unknown-linux-gnu --cpu=x86-64-v3",
    "//conditions:default": "--target=arm64-apple-macosx14.0.0 --cpu=apple-m1",
})
