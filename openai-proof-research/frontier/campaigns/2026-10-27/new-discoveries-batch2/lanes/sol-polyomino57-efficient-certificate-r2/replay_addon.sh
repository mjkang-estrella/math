#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/addon"
mkdir -p work logs
cd work
for module in Grid Growth Normalization Bounds Witness Efficient Coverage Existence ListCertificate Assembly SmallClosure SortedCertificate FastSmallClosure AddonAudit; do
  cp "../formal/$module.lean" .
  python3 ../run.py -o "$module.olean" "$module.lean" > "../logs/$module.log" 2>&1
  echo "PASS addon $module"
done
