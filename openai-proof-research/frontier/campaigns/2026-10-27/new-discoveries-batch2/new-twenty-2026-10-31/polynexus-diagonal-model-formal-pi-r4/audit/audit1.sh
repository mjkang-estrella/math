#!/usr/bin/env bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$LANE/env.sh"
exec "$LEAN_BIN/lean" -DwarningAsError=true "$@"
