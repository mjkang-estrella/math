#!/bin/bash
# Fresh extracted strict replay of the MathDB 374241 Lean packet.
# Copies only the source files into a new empty directory, rebuilds in dependency order with
# -DwarningAsError=true, runs the axiom audit and leanchecker on every module.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="$HERE/fresh-replay"
rm -rf "$OUT"; mkdir -p "$OUT"
for f in CycDefs CycRot CycLower CycUpper CycMain Audit; do cp "$HERE/$f.lean" "$OUT/"; done
sha256sum "$OUT"/*.lean > "$OUT/sources.sha256"
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PK/mathlib/.lake/build/lib/lean:$PK/plausible/.lake/build/lib/lean:$PK/LeanSearchClient/.lake/build/lib/lean:$PK/importGraph/.lake/build/lib/lean:$PK/proofwidgets/.lake/build/lib/lean:$PK/aesop/.lake/build/lib/lean:$PK/Qq/.lake/build/lib/lean:$PK/batteries/.lake/build/lib/lean:$OUT"
export PATH="$BIN:/usr/bin:/bin"
cd "$OUT"
ulimit -c 0; ulimit -t 120
for f in CycDefs CycRot CycLower CycUpper CycMain; do
  taskset -c 0,1 lean -j1 -M4096 -DwarningAsError=true -o "$f.olean" "$f.lean" > "$f.build.log" 2>&1; rc=$?
  echo "$f build rc=$rc"
done
taskset -c 0,1 lean -j1 -M4096 -DwarningAsError=true Audit.lean > audit.log 2>&1; echo "Audit rc=$?"
for f in CycDefs CycRot CycLower CycUpper CycMain; do
  taskset -c 0,1 leanchecker "$f" > "$f.leanchecker.log" 2>&1; echo "$f leanchecker rc=$?"
done
grep -n "sorry\|admit\|native_decide\|ofReduceBool\|unsafe\|^axiom\| axiom " *.lean > keyword-scan.txt || echo "keyword scan: no matches" > keyword-scan.txt
cat keyword-scan.txt
