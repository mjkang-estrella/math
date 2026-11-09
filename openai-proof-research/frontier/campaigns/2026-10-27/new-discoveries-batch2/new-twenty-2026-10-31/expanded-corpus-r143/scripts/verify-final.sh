#!/bin/bash
set -euo pipefail
./scripts/lean.sh -DwarningAsError=true -o TorusPMD.olean TorusPMD.lean > outputs/lean-final.log 2>&1
./scripts/lean.sh -DwarningAsError=true AuditAll.lean > outputs/axioms-all.log 2>&1
./scripts/check.sh TorusPMD > outputs/leanchecker.log 2>&1
cp TorusPMD.lean Audit.lean AuditAll.lean packet/
tar --sort=name --mtime='UTC 2026-11-04' --owner=0 --group=0 --numeric-owner -czf lean-packet.tar.gz -C packet .
mkdir replay-final
tar -xzf lean-packet.tar.gz -C replay-final
(cd replay-final && ./scripts/lean.sh -DwarningAsError=true -o TorusPMD.olean TorusPMD.lean) > outputs/replay-final-build.log 2>&1
(cd replay-final && ./scripts/lean.sh -DwarningAsError=true AuditAll.lean) > outputs/replay-final-axioms.log 2>&1
(cd replay-final && ./scripts/check.sh TorusPMD) > outputs/replay-final-leanchecker.log 2>&1
sha256sum lean-packet.tar.gz TorusPMD.lean > outputs/packet-sha256.txt
printf 'All final checks exited 0\n' > outputs/verification-status.txt
