#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
exec python3 capped_run.py "$@"
