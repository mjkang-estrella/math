#!/bin/bash
# each arg: "mode parts..." ; runs sequentially, prints summaries
cd "$(dirname "$0")/.."
for spec in "$@"; do echo "### $spec"; tmp/xray.bin $spec | grep -v "^DEFICIENT" | tail -5; done
