#!/bin/bash
set -euo pipefail
LANE=$(cd "$(dirname "$0")" && pwd)
cd "$LANE/work"
{ while read -r m; do echo "lean/$m.lean"; done < modules.txt
  printf '%s\n' modules.txt round1-modules.txt round2-prefix.txt
  printf '%s\n' scripts/cap.sh scripts/env.sh scripts/check.sh scripts/replay.sh scripts/replay-prefix.sh scripts/replay-certificate.sh scripts/source-scan.sh
} > package-files.txt
while read -r f; do sha256sum "$f"; done < package-files.txt > source-files.sha256
rm -f "$LANE/source.zip"
{ cat package-files.txt; echo source-files.sha256; } | zip -q "$LANE/source.zip" -@
sha256sum "$LANE/source.zip" > "$LANE/logs/source-zip.sha256"
