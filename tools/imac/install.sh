#!/bin/sh
# Installs the iMac build limits for every worktree on this machine:
#
#   ~/.local/bin/bazelq   the FIFO build queue (a copy of tools/imac/bazelq)
#   ~/.local/bin/bazel    a shim that sends bare `bazel` through bazelq
#   ~/.bazelrc            --jobs=6 and matching resource limits, between
#                         "pia-imac" markers (the rest of the file is kept)
#   ~/.cache/bazelq/slots how many queued commands run at once
#
# Run it again after tools/imac changes:  sh tools/imac/install.sh [SLOTS]
# ~/.local/bin must come before the real Bazel on PATH.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
bin="$HOME/.local/bin"
slots="${1:-1}"

mkdir -p "$bin" "$HOME/.cache/bazelq"
cp "$here/bazelq" "$bin/bazelq.new" && chmod +x "$bin/bazelq.new" && mv "$bin/bazelq.new" "$bin/bazelq"

cat > "$bin/bazel.new" <<'EOF'
#!/bin/sh
# BAZELQ_SHIM: sends every bazel command through the machine-wide build
# queue. Installed by pia-lang tools/imac/install.sh; remove this file to
# go back to the real bazel.
exec "$HOME/.local/bin/bazelq" "$@"
EOF
chmod +x "$bin/bazel.new" && mv "$bin/bazel.new" "$bin/bazel"

echo "$slots" > "$HOME/.cache/bazelq/slots"

rc="$HOME/.bazelrc"
touch "$rc"
tmp="$rc.new"
sed '/^# >>> pia-imac/,/^# <<< pia-imac/d' "$rc" > "$tmp"
cat >> "$tmp" <<'EOF'
# >>> pia-imac (written by pia-lang tools/imac/install.sh; edits here are lost)
# At most 6 actions at a time per build, on every worktree. bazelq decides
# how many builds run at once. Memory, not CPU, is what runs out first on
# this 16 GB machine: every worktree's Bazel server holds about 1 GB, so an
# idle one exits after 15 minutes.
startup --max_idle_secs=900
build --jobs=6
build --local_resources=cpu=6
build --local_resources=memory=HOST_RAM*.4
test --local_test_jobs=6
# piac solves on one thread per core by default; 2 threads each keeps 6
# tests at once near the machine's 8 cores, since few saturate both.
test --test_env=PIA_JOBS=2
# <<< pia-imac
EOF
mv "$tmp" "$rc"

echo "installed: $bin/bazelq, $bin/bazel (shim), $rc, slots=$slots"
case "$(command -v bazel)" in
  "$bin/bazel") ;;
  *) echo "warning: \`bazel\` on PATH is $(command -v bazel), not the shim; put $bin first" >&2 ;;
esac
