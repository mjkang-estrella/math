set -eu
cd "$(dirname "$0")/.."
for n in 5 6 7 8; do
 python3 -I scripts/guard.py "exhaustive-$n" python3 -I "$PWD/scripts/exhaustive.py" "$n"
done
