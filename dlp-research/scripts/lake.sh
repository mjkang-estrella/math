#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
local_lake="$project_dir/.tools/lean-4.34.1-linux/bin/lake"
if [[ -x "$local_lake" ]]; then
  exec "$local_lake" "$@"
fi
if command -v lake >/dev/null 2>&1; then
  exec lake "$@"
fi
echo 'Lean is missing. Install elan using https://lean-lang.org/install/ and rerun this command.' >&2
exit 1
