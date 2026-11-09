#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
while read -r m; do
 if ! test -f "$R/packet/build/$m.olean"; then bash "$R/build.sh" "$m"; fi
done < "$1"
