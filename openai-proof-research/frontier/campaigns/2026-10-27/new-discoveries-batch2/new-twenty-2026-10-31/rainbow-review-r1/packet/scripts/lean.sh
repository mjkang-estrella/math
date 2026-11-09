#!/bin/bash
set -eu
printf "COMMAND" >&2; printf " %q" "$@" >&2; printf "\n" >&2
export TMPDIR="$(cd ..; pwd)/tmp" XDG_CACHE_HOME="$(cd ..; pwd)/cache"
pkg=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$(find "$pkg" -path '*/.lake/build/lib/lean' -type d | paste -sd:):$PWD"
exec ./scripts/run /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -M3500 "$@"
