#!/bin/bash
set -eu
cd "$(dirname "$0")"
export LEAN_PATH=.:$(cat leanpath.txt)
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true -j2 "$@"
