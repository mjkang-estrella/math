#!/bin/bash
# Orchestrator for lane common-basis-audit-supplement-pi-r3 (review sub-agent, Pi GLM-5.3-Flash).
# Narrow formal-audit supplement: closes the two root-identified evidence gaps of
# common-basis-fidelity-pi-r2. No writes outside this lane; imported build dir is read-only.
set -eu
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/common-basis-audit-supplement-pi-r3
R2=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/common-basis-fidelity-pi-r2
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin

export PATH="$BIN:/usr/local/bin:/usr/bin:/bin"
export LEAN_PATH="$LANE/audit-build:$R2/audit/pi-r2-build:$(find "$PKG" -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
# HOME left as the user's actual HOME; no cache priming; python run with -I -B.

RUN="python3 -I -B $LANE/scripts/pi_r3_runner.py"
cd "$LANE"
mkdir -p audit-build logs receipts

{
echo "== lane common-basis-audit-supplement-pi-r3 orchestration $(date -u +%FT%TZ)"
echo "LEAN_PATH=$LEAN_PATH"
echo "PATH=$PATH"
echo "lean --version: $("$BIN/lean" --version)"
echo "mathlib HEAD: $(git -C "$PKG/mathlib" rev-parse HEAD 2>/dev/null || echo 'git unavailable')"
for t in lean leanc leanchecker; do echo "sha256($t)=$(sha256sum "$BIN/$t" | cut -d' ' -f1)"; done
} > receipts/toolchain-env.txt

echo "[1/6] frozen-input verification (before)"
python3 -I -B "$LANE/scripts/verify_frozen_r3.py" before

echo "[2/6] strict compile of audit supplement (lane-only olean output)"
$RUN lean-Supplement "$BIN/lean" -j1 -M3500 -DwarningAsError=true \
  -o "$LANE/audit-build/Supplement.olean" "$LANE/audit-src/Supplement.lean"

echo "[3/6] leanchecker on the new supplement olean"
$RUN checker-Supplement "$BIN/leanchecker" Supplement

echo "[4/6] negative control: sorryAx detection (no warningAsError; warning is the signal)"
$RUN lean-CtrlSupp "$BIN/lean" -j1 -M3500 "$LANE/audit-src/CtrlSupp.lean"

echo "[5/6] frozen-input verification (after)"
python3 -I -B "$LANE/scripts/verify_frozen_r3.py" after

echo "[6/6] hash manifest of lane artifacts"
find "$LANE" -type f ! -name 'manifest.sha256' ! -path '*/audit-build/*' -print0 \
  | sort -z | xargs -0 sha256sum > "$LANE/manifest.sha256"
sha256sum "$LANE/audit-build/Supplement.olean" >> "$LANE/manifest.sha256"
echo "manifest entries: $(wc -l < "$LANE/manifest.sha256")"
echo ORCHESTRATION-OK
