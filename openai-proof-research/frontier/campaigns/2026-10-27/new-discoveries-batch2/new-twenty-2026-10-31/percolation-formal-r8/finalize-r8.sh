#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
cd "$R"
test -f strict-final/logs/AuditR8.ok
bash guard-r8.sh report-final python3 -I -B report-r8.py
bash guard-r8.sh scan-final python3 -I -B scan-r8.py strict-final
sed -n '/^{/,/^}/p' logs/scan-final.log > source-scan.json
bash guard-r8.sh package-final-preverify python3 -I -B package-r8.py
bash guard-r8.sh verify-final-package python3 -I -B verify-package-r8.py
bash guard-r8.sh refresh-final-results python3 -I -B refresh-results-r8.py
bash guard-r8.sh package-final python3 -I -B package-r8.py
bash guard-r8.sh final-integrity python3 -I -B final-integrity-r8.py
