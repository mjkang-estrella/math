#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/extracted"
mkdir work logs
cd work
for module in Grid Growth Normalization Bounds Witness Pilot Efficient Coverage Existence ListCertificate Assembly NumericPilot SmallClosure PlacementTree OriginAudit; do
  cp "../formal/$module.lean" .
  python3 ../run.py -o "$module.olean" "$module.lean" > "../logs/$module.log" 2>&1
  echo "PASS $module"
done
for source in ../formal/Terminal*.lean; do
  module="$(basename "$source" .lean)"
  cp "$source" .
  python3 ../run.py -o "$module.olean" "$module.lean" > "../logs/$module.log" 2>&1
  audit="Audit$module"
  cp "../formal/$audit.lean" .
  python3 ../run.py -o "$audit.olean" "$audit.lean" > "../logs/$audit.log" 2>&1
  echo "PASS $module + actual-origin audit"
done
