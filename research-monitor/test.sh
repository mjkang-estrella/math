#!/usr/bin/env bash
# Run all monitor tests (temp fixture repos only; live research files are never modified).
set -euo pipefail
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
PYTHONDONTWRITEBYTECODE=1 timeout 180 python3 -m unittest discover -s tests -t . "$@"
timeout 60 node --test tests/estimator.test.cjs tests/scenario.test.cjs
