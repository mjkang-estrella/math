#!/bin/bash
# usage: leanenv.sh DIR cmd...   (runs a Lean tool in DIR with the pinned Mathlib cache, read-only, on LEAN_PATH)
DIR="$1"; shift
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PK/mathlib/.lake/build/lib/lean:$PK/plausible/.lake/build/lib/lean:$PK/LeanSearchClient/.lake/build/lib/lean:$PK/importGraph/.lake/build/lib/lean:$PK/proofwidgets/.lake/build/lib/lean:$PK/aesop/.lake/build/lib/lean:$PK/Qq/.lake/build/lib/lean:$PK/batteries/.lake/build/lib/lean:$DIR"
export PATH="/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin"
cd "$DIR" && exec "$@"
