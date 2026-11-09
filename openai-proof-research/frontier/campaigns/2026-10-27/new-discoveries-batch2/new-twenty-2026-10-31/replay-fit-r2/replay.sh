#!/bin/bash
set -eu
cd "$(dirname "$0")"
name=${1:-development}
[[ "$name" =~ ^[A-Za-z0-9-]+$ ]]
mkdir -p "$name"
for f in source/*.lean; do
 dest="$name/${f##*/}"
 if [ -f "$dest" ]; then cmp "$f" "$dest"; else cp "$f" "$dest"; fi
done
cd "$name"
source ../env.sh
while read -r m; do
 [ -f "$L/logs/$name-$m.ok" ] && [ -f "$m.olean" ] && continue
 echo "Building $name $m"
 "$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$L/logs/$name-$m.build.log" 2>&1 || exit 1
 "$L/run" "$BIN/leanchecker" "$m" > "$L/logs/$name-$m.check.log" 2>&1 || exit 1
 touch "$L/logs/$name-$m.ok"
done < "$L/modules.txt"
