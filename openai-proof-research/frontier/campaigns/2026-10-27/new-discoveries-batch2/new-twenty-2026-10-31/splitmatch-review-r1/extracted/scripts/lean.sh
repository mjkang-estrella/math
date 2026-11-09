#!/bin/bash
set -eu
formal=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal
export LEAN_PATH="${PACKET_MODULE_DIR:-/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r168/replay}:"$(find "$formal/.lake/packages" -path '*/.lake/build/lib/lean' -type d | paste -sd:)
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -M3500 -DwarningAsError=true "$@"
