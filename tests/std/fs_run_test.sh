#!/usr/bin/env bash
# Runs the pia_binary `fs_run`, whose exit status is its verdict, in the
# test's own temporary directory, where it writes and removes fs.tmp.
bin="$PWD/$1"
cd "$TEST_TMPDIR" && exec "$bin"
