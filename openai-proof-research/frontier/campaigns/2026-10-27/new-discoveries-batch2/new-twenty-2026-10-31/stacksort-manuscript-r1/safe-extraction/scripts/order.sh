#!/bin/bash
set -eu
cd "$(dirname "$0")/../src"
for f in *.lean; do
 m=${f%.lean}; echo "$m $m"
 sed -n 's/^import \(StackSort[^ ]*\).*$/\1/p' "$f" | while read -r d; do echo "$d $m"; done
done | tsort
