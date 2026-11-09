#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
RUN="$(date -u +%Y%m%dT%H%M%S)-$$"
for M in GridLadderLayers GridLadderOrbit GridOrdinaryLayers GridBorderWalk GridSideColors GridFinal5 Audit5; do
  LEAN_TOOL=leanchecker scripts/lean.sh "$M" > "logs/$RUN-checker-$M.log" 2>&1
  sha256sum "src/$M.lean" | cut -d' ' -f1 > "build/$M.replay-ok"
  echo "CHECKED $M"
done
