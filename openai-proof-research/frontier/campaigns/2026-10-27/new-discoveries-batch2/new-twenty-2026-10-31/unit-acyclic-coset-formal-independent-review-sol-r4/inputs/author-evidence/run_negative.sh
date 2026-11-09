#!/bin/bash
set -u
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
for probe in WrongIndicator WrongUnit WrongAcyclic; do
  bash "$LANE/audit.sh" "$probe"
  rc=$?
  if [ "$rc" -ne 1 ]; then exit 42; fi
  echo "EXPECTED_FAILURE $probe EXIT=$rc"
done
