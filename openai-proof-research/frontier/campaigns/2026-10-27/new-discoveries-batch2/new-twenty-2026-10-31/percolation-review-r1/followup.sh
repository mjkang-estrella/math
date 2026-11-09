#!/bin/bash
set -eu
cd "$(dirname "$0")"
# Run only after every previously launched heavy process has terminated.
./guard.sh controls-serial python3 -I "$PWD/mathcheck.py" controls
./guard.sh encode-serial python3 -I "$PWD/mathcheck.py" encode
set +e
./guard.sh solver-serial /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical --lrat=true --binary=false independent.cnf independent-serial.lrat
rc=$?
set -e
[ "$rc" = 20 ]
./guard.sh proof-serial python3 -I "$PWD/checkproof.py" "$PWD/independent.cnf" "$PWD/independent-serial.lrat" proof-serial
mkdir -p first-replay-logs
mv logs/lean-* logs/checker-* first-replay-logs/
mv build first-build
./replay.sh
