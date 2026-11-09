#!/usr/bin/env bash
# Start the monitor detached from this terminal; PID in .run/server.pid, log in .run/server.log.
set -euo pipefail
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$here/.run"
if [[ -f "$here/.run/server.pid" ]] && kill -0 "$(cat "$here/.run/server.pid")" 2>/dev/null; then
  echo "already running (pid $(cat "$here/.run/server.pid"))"; exit 0
fi
cd "$here"
setsid nohup python3 -m monitor.server --pid-file "$here/.run/server.pid" "$@" >"$here/.run/server.log" 2>&1 </dev/null &
for _ in $(seq 1 50); do [[ -s "$here/.run/server.pid" ]] && break; sleep 0.1; done
if [[ -s "$here/.run/server.pid" ]]; then head -1 "$here/.run/server.log"; echo "pid $(cat "$here/.run/server.pid")"; else cat "$here/.run/server.log"; exit 1; fi
