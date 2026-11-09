#!/bin/bash
set -eu
for i in 0 1; do
 for x in {0..7}; do
  m=C${i}R${x}
  ./scripts/lean.sh -DwarningAsError=true -o "$m.olean" "$m.lean" > "logs/$m.log" 2>&1
  echo "$m PASS"
 done
done
./scripts/lean.sh -DwarningAsError=true -o Certificates.olean Certificates.lean > logs/certassembly.log 2>&1
./scripts/lean.sh -DwarningAsError=true -o Final.olean Final.lean > logs/final.log 2>&1
