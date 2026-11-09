#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
bash scripts/check.sh Chord5Graph
