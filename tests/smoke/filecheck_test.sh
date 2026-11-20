#!/usr/bin/env bash
# Runs a .mlir file's `// RUN: pia-opt %s | FileCheck %s` line.
# Usage: filecheck_test.sh <pia-opt> <FileCheck> <test.mlir>
set -euo pipefail
pia_opt="$1"
filecheck="$2"
input="$3"
"$pia_opt" "$input" | "$filecheck" "$input"
