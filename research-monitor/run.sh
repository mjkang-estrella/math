#!/usr/bin/env bash
# Start the read-only research monitor on loopback (default port 8765).
# Usage: ./run.sh [--port N] [--interval SECONDS] [--allow-host NAME] ...
set -euo pipefail
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
exec python3 -m monitor.server "$@"
