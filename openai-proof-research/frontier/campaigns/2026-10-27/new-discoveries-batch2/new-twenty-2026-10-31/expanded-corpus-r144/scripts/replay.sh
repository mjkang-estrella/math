#!/bin/bash
set -eu
cd "$(dirname "$0")/../replay"
for m in Base C0R{0..7} C1R{0..7} Certificates Final Semantics; do
 ./scripts/lean.sh -DwarningAsError=true -o "$m.olean" "$m.lean" > "logs/build-$m.log" 2>&1
 ./scripts/check.sh "$m" > "logs/check-$m.log" 2>&1
 echo "$m BUILD_AND_CHECK_PASS"
done
./scripts/lean.sh -DwarningAsError=true Audit.lean > logs/audit.log 2>&1
echo AUDIT_PASS
