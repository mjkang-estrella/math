#!/bin/bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
PACK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build:$PACK/mathlib/.lake/build/lib/lean:$PACK/batteries/.lake/build/lib/lean:$PACK/aesop/.lake/build/lib/lean:$PACK/Qq/.lake/build/lib/lean:$PACK/proofwidgets/.lake/build/lib/lean:$PACK/importGraph/.lake/build/lib/lean:$PACK/LeanSearchClient/.lake/build/lib/lean:$PACK/plausible/.lake/build/lib/lean"
LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export PATH="$LEAN_BIN:$PATH"
