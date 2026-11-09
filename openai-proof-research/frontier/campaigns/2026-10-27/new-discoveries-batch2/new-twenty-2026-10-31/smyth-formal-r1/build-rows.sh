#!/usr/bin/env bash
set -e
for f in src/S[0-9][0-9].lean src/T[0-9][0-9].lean; do
 m=$(basename "$f" .lean)
 [ -f "build/$m.olean" ] && continue
 ./capped.sh lean -M3500 -DwarningAsError=true -o "build/$m.olean" "$f" > "logs/$m.log" 2>&1 || { cat "logs/$m.log"; exit 1; }
 echo "$m OK"
done
