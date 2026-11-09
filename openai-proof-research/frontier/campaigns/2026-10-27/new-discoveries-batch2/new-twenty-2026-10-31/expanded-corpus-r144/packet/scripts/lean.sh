#!/bin/bash
set -eu
pkg=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$(find "$pkg" -path '*/.lake/build/lib/lean' -type d | paste -sd:):$PWD"
exec ./scripts/run /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -M3500 "$@"
