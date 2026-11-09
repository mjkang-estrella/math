#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
bash "$R/run-new.sh" "$R/geometry-order.txt"
head -38 "$R/packet/module-order.txt" > "$R/base-order.txt"
bash "$R/run-new.sh" "$R/base-order.txt"
bash "$R/build.sh" Normalize NormalizedExport
