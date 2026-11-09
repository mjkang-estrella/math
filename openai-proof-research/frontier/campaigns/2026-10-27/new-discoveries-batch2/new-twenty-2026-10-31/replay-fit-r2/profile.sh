#!/bin/bash
set -eu
cd "$(dirname "$0")/profile"
source ../env.sh
"$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true -o SpectralWitness.olean SpectralWitness.lean > "$L/logs/original-profile.log" 2>&1
