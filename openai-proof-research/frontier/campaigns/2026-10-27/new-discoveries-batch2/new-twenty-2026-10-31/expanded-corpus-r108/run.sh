#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
export PYTHONDONTWRITEBYTECODE=1
export TMPDIR="$PWD/tmp"
mkdir -p tmp logs outputs
python scripts/limited.py strict-replay-reproduce python scripts/replay.py
python scripts/certificate.py
python scripts/report.py
python scripts/validate.py
