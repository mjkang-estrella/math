#!/bin/bash
set -eu
lane=$(cd "$(dirname "$0")" && pwd)
packet=${PACKET:-$lane/packet}
mkdir -p "$packet/build"
export LEAN_PATH="$packet/build"
while read -r m; do
 test -n "$m" || continue
 "$lane/guard.sh" "build-$m" lean -M3500 -DwarningAsError=true -o "$packet/build/$m.olean" "$packet/src/$m.lean" || exit $?
 "$lane/guard.sh" "check-$m" leanchecker "$m" || exit $?
done < "${ORDER:-$packet/module-order.txt}"
