#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
count=0
while read -r h f; do
 [[ $f == lean/*.lean ]] || continue
 actual=$(sha256sum "fresh/$f"); actual=${actual%% *}
 [[ $h == "$actual" ]] || { echo "MISMATCH $f"; exit 1; }
 count=$((count+1))
done < round1-source-files.sha256
echo "$count unchanged Lean files"
