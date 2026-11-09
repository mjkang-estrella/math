#!/bin/bash
set -eu
cd "$(dirname "$0")"
export LEAN_PATH="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:$PWD"
ulimit -c 0
ulimit -t 180
exec taskset -c 0,1 /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -M4096 -DwarningAsError=true "$@"
