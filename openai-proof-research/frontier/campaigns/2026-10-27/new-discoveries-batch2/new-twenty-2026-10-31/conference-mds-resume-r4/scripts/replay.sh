#!/usr/bin/env bash
# Fresh extracted replay. Usage: replay.sh <packet_dir> <fresh_empty_dir>
set -euo pipefail
PK=$(realpath "$1"); OUT="$2"; mkdir "$OUT"; OUT=$(realpath "$OUT"); cd "$OUT"
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
CHK=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
mkdir src build
cp "$PK"/audit/Controls.lean src/; cp "$PK"/scripts/{gen_lean.py,Template.lean,verify_from_scratch.py,make_certificates.py} "$PK"/data/cex20_certificate.json "$PK"/audit/Audit.lean src/
cp "$PK"/lean/ConferenceMDS324342.lean src/packet.lean
# regenerate data + Lean from the frozen matrix alone
python3 -I src/verify_from_scratch.py src/cex20_certificate.json src/vfs.json > verify.log
python3 -I src/make_certificates.py src/cex20_certificate.json src/vfs.json src/lean_cert.json > certs.log
python3 -I src/gen_lean.py src/lean_cert.json build/ConferenceMDS324342.lean
cmp build/ConferenceMDS324342.lean src/packet.lean && echo "regenerated Lean identical to packet" > regen.log
# forbidden-token scan (comments included)
if grep -n -E '\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|extern|opaque|partial|@\[csimp\]|debug|set_option)\b' build/ConferenceMDS324342.lean > forbidden.txt; then echo FORBIDDEN; cat forbidden.txt; exit 3; fi
LP="$OUT/build:"; for d in $P/*/; do LP="$LP${d}.lake/build/lib/lean:"; done
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
run() { systemd-run --user --scope -q -p MemoryMax=12G -p CPUQuota=200% env LEAN_PATH="$LP" taskset -c 0,1 timeout 1500 "$@"; }
cd build
/usr/bin/time -v -o ../time-main.txt bash -c "$(declare -f run); LP='$LP'; run $LEAN -DwarningAsError=true -j2 -o ConferenceMDS324342.olean ConferenceMDS324342.lean" > ../main.stdout 2> ../main.stderr
cp ../src/Audit.lean .
/usr/bin/time -v -o ../time-audit.txt bash -c "$(declare -f run); LP='$LP'; run $LEAN -DwarningAsError=true -j2 Audit.lean" > ../audit.stdout 2> ../audit.stderr
/usr/bin/time -v -o ../time-checker.txt bash -c "$(declare -f run); LP='$LP'; run $CHK ConferenceMDS324342" > ../checker.stdout 2> ../checker.stderr || echo "leanchecker exit $?" >> ../checker.stderr
/usr/bin/time -v -o ../time-controls.txt bash -c "$(declare -f run); LP='$LP'; cp ../src/Controls.lean .; run $LEAN -DwarningAsError=true -j2 Controls.lean" > ../controls.stdout 2> ../controls.stderr
cd ..
sha256sum build/ConferenceMDS324342.lean build/ConferenceMDS324342.olean build/Audit.lean src/* > SHA256SUMS
echo DONE
