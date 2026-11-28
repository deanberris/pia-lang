#!/bin/sh
# Sets up a Claude Code cloud session to build and test Pia with Bazel.
#
# The cloud environment's setup script runs this as root once per fresh
# container (docs/cloud.md). It installs Bazelisk as `bazel`, which fetches
# the Bazel in .bazelversion, and turns on --config=cloud in user.bazelrc:
# the container has 4 cores, too few to build LLVM, so every action runs on
# BuildBuddy's executors, as CI's Linux job does. The API key comes from the
# environment's BUILDBUDDY_API_KEY variable at build time, through
# tools/cloud/buildbuddy-credential-helper, so it is never written here.
set -eu

BAZELISK_VERSION=1.27.0
BAZELISK_SHA256=e1508323f347ad1465a887bc5d2bfb91cffc232d11e8e997b623227c6b32fb76

repo=$(cd "$(dirname "$0")/../.." && pwd)

if ! command -v bazel >/dev/null 2>&1; then
  tmp=$(mktemp)
  curl -fsSL -o "$tmp" \
    "https://github.com/bazelbuild/bazelisk/releases/download/v$BAZELISK_VERSION/bazelisk-linux-amd64"
  echo "$BAZELISK_SHA256  $tmp" | sha256sum -c - >/dev/null
  install -m 0755 "$tmp" /usr/local/bin/bazel
  rm -f "$tmp"
fi

# user.bazelrc is ignored by git, so a session's own overrides stay local.
if ! grep -qs -- '--config=cloud' "$repo/user.bazelrc"; then
  echo "common --config=cloud" >>"$repo/user.bazelrc"
fi

# Fetch Bazel itself now, so the first build does not wait for it.
(cd "$repo" && bazel --version)
