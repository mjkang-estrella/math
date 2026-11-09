#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
export LEAN_PATH="$R/packet/build"
mkdir -p "$LEAN_PATH"
for m in "$@"; do
 bash "$R/guard.sh" "dev-$m" lean -M3500 -DwarningAsError=true -o "$LEAN_PATH/$m.olean" "$R/packet/src/$m.lean"
 bash "$R/guard.sh" "devcheck-$m" leanchecker "$m"
done
