#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
source env.sh
mkdir -p build logs tmp
while IFS= read -r module; do
 [ -z "$module" ] && continue
 if [ "${1:-}" = resume ] && [ -f "logs/$module.replayed" ]; then continue; fi
 echo "Compiling $module"
 ./bounded.sh lean -M3500 -DwarningAsError=true -o "build/$module.olean" "$module.lean" > "logs/$module.compile.log" 2>&1
 echo "Checking $module"
 ./bounded.sh leanchecker "$module" > "logs/$module.checker.log" 2>&1
 touch "logs/$module.replayed"
done < module-order.txt
