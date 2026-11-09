#!/bin/bash
set -eu
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-review-r1
export LEAN_PATH="$PWD/build/lean"
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
for p in "$P"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
mkdir -p own-bin
cat > own-bin/lean <<'INNER'
#!/bin/bash
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -M3500 -j1 "$@"
INNER
chmod +x own-bin/lean
export PATH="$PWD/own-bin:$PATH"
for m in Definitions Arithmetic Certificate EdgeRows{0..7} Endpoint; do
 echo "BUILD $m $(date -Is)"
 ./cap.sh lean -DwarningAsError=true -o "build/lean/$m.olean" "build/lean/$m.lean" >"logs/lean-$m.log" 2>&1
 echo "CHECK $m $(date -Is)"
 ./cap.sh leanchecker "$m" >"logs/check-$m.log" 2>&1
 echo "PASS $m"
done
./cap.sh lean -DwarningAsError=true build/lean/Audit.lean >logs/audit.log 2>&1
./cap.sh lean -DwarningAsError=true build/lean/Inventory.lean >logs/inventory.log 2>&1
