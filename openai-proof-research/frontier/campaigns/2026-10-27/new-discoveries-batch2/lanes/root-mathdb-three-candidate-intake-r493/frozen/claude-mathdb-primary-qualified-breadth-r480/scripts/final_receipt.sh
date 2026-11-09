#!/bin/bash
# Separately executed final receipt: three guarded verifier runs incl. on-disk negative test; JSON assembled under guard.
cd "$1" || exit 2
V() { scripts/g.sh verify.py "$PWD" "$@" 2>&1; echo "EXIT=$?"; }
T0=$(date -u +%FT%TZ); A=$(V --negative-test)
touch NEGATIVE-TEST-STRAY.tmp; B=$(V); rm -f NEGATIVE-TEST-STRAY.tmp
C=$(V); T1=$(date -u +%FT%TZ)
esc() { printf '%s' "$1" | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g' | awk 'BEGIN{ORS="\\n"}{print}'; }
printf '{"receipt":"r480 final receipt (separately executed after manifest)","utc_start":"%s","utc_end":"%s","command":"scripts/final_receipt.sh LANE -> scripts/g.sh verify.py LANE [--negative-test] (helper_guard 512MiB/CPU210s/wall230s)","note":"Run 2 is an on-disk negative test: stray lane file NEGATIVE-TEST-STRAY.tmp created, verifier expected nonzero, file removed. Prior attempt preserved in failures/F02.","run_1_with_in_memory_negative_tests":"%s","run_2_on_disk_stray_file_expect_nonzero":"%s","run_3_after_removal_expect_zero":"%s"}' "$T0" "$T1" "$(esc "$A")" "$(esc "$B")" "$(esc "$C")" | scripts/g.sh scripts/receipt_json.py "$PWD/final-receipt.json"
