#!/bin/bash
# Usage: lean1.sh DIR ARGS...  -- runs Lean 4.34.1 in DIR with LEAN_PATH = pinned Mathlib cache + DIR.
set -u
D="$1"; shift
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP=""
for p in mathlib plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries; do LP="$LP$PK/$p/.lake/build/lib/lean:"; done
export LEAN_PATH="$LP$D"
export PATH="$BIN:/usr/bin:/bin"
cd "$D"
exec "$@"
