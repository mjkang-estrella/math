#!/usr/bin/env bash
# Stop a monitor started with start-bg.sh.
set -euo pipefail
pidfile="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/.run/server.pid"
[[ -s "$pidfile" ]] || { echo "not running (no pid file)"; exit 0; }
pid="$(cat "$pidfile")"
kill "$pid" 2>/dev/null && echo "stopped $pid" || echo "process $pid not running"
rm -f "$pidfile"
