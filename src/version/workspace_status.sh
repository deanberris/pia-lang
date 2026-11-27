#!/bin/sh
# Bazel's workspace status for release builds (`--config=release`, ADR
# 0073): piac's version is the release version from MODULE.bazel, the
# number of commits on the branch and the short commit. Run from the
# workspace root. Prints nothing outside a git checkout, so the build is
# `dev`. CI checks out the whole history, or the count would be 1.
base=$(sed -n 's/^module(name = "pia", version = "\(.*\)")$/\1/p' MODULE.bazel)
count=$(git rev-list --count HEAD 2>/dev/null) || exit 0
sha=$(git rev-parse --short=12 HEAD 2>/dev/null) || exit 0
echo "STABLE_PIA_VERSION ${base:-0.0.0}+$count.$sha"
