set -eu
cd "$(dirname "$0")/.."
L=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
python3 -I scripts/guard.py reviewer-controls "$L/lean" -j1 -DwarningAsError=true ReviewerControls.lean
python3 -I scripts/guard.py reviewer-audit "$L/lean" -j1 -DwarningAsError=true ReviewerAudit.lean
python3 -I scripts/guard.py checker-restatement "$L/leanchecker" ReviewerRestatement
for m in ReviewerWrongValue ReviewerGroupAsMP ReviewerPerturbed; do
 if python3 -I scripts/guard.py "negative-$m" "$L/lean" -j1 -DwarningAsError=true "../negative/$m.lean"; then exit 1; fi
done
