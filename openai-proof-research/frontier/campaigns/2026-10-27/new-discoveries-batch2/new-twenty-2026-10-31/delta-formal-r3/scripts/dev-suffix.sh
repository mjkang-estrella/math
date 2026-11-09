#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
while read -r m; do
 bash source/scripts/check.sh "$m"
 echo "CHECKED $m"
done < <(sed -n '/^Closure283$/,$p' source/modules.txt)
