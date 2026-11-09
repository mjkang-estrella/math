LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ebc-formal-r2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" MALLOC_ARENA_MAX=2
PKGS=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build"
for p in "$PKGS"/*; do LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export LEAN_PATH
cap() { (ulimit -t 120; perl "$LANE/scripts/cap.pl" taskset -c 0,1 "$@"); }
