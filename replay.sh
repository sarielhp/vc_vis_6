#!/bin/sh
# Replay the DRAT certificates for all 74 hull cases (or the given case IDs).
# Usage, from anywhere:  sh replay.sh [CASE_ID ...]
# Requires: a C compiler, Julia, and the QuickEnv.jl package.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
scratch="${TMPDIR:-/tmp}/$(id -un)/vc_vis_6_replay"
mkdir -p "$scratch"
check=$(mktemp -d "$scratch/run.XXXXXXXX")
cc -std=gnu99 -O2 "$root/certificates/drat-trim/drat-trim.c" -o "$check/drat-trim"
cd "$root/certificates"
TMPDIR="$check" julia replay.jl "$check" "$check/drat-trim" "$@"
printf 'Checker logs: %s\n' "$check"
