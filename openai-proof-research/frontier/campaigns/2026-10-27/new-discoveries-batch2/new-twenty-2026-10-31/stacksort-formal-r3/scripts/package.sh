#!/bin/bash
set -eu
zip -q stacksort-source3.zip src/*.lean scripts/run.sh scripts/build.sh scripts/replay.sh scripts/order.txt scripts/check_audit.py
mkdir fresh-extraction
unzip -q stacksort-source3.zip -d fresh-extraction
mkdir -p fresh-extraction/{tmp,cache,logs}
cd fresh-extraction
bash scripts/replay.sh
