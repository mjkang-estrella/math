#!/usr/bin/env bash
set -euo pipefail
lane=$(cd -- "$(dirname -- "$0")" && pwd)
packages=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$lane/formal"
for dep in mathlib batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible Cli; do
  LEAN_PATH="$LEAN_PATH:$packages/$dep/.lake/build/lib/lean"
done
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean "$@"
