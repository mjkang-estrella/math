#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
cd "$R"
mkdir -p build logs tmp cache
export LEAN_PATH="$R/build"
sig=round4-rolling-v1
started=$SECONDS
completed=0
while read -r m; do
 test -n "$m" || continue
 sig=$(printf '%s\n%s\n' "$sig" "$(sha256sum "src/$m.lean" | cut -d' ' -f1)" | sha256sum | cut -d' ' -f1)
 case "$m" in *[!a-zA-Z0-9_]*) exit 2;; esac
 if test "${RESUME:-0}" = 1 && test -f "logs/$m.ok" && test -f "build/$m.olean" && test "$(cat "logs/$m.ok")" = "$sig"; then completed=$((completed+1)); continue; fi
 if test "${BUDGET:-0}" -gt 0 && test "$((SECONDS-started))" -ge "$BUDGET"; then printf 'Budget reached before %s; resume with RESUME=1.\n' "$m"; exit 0; fi
 bash ./guard.sh "build-$m" lean -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
 bash ./guard.sh "check-$m" leanchecker "$m"
 printf '%s\n' "$sig" > "logs/$m.ok"
 completed=$((completed+1))
 printf '{"completed_modules":%s,"last_module":"%s","source_digest":"%s"}\n' "$completed" "$m" "$sig" > replay-progress.json.new
 mv replay-progress.json.new replay-progress.json
 if test -f replay-frontiers.tsv; then
  row=$(awk -v m="$m" '$1==m {print $2,$3,$4}' replay-frontiers.tsv)
  if test -n "$row"; then
   read -r steps last next <<< "$row"
   printf '{"replayed_steps":%s,"last_lrat_id":%s,"next_index_zero_based":%s,"next_lrat_id":%s,"total_steps":129671}\n' "$steps" "$last" "$steps" "$next" > normalized-progress.json.new
   mv normalized-progress.json.new normalized-progress.json
  fi
 fi
done < module-order.txt
printf 'Strict replay complete: %s modules.\n' "$completed"
