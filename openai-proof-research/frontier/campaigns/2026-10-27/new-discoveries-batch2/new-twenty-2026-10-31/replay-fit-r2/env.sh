L=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export PATH="$BIN:/usr/bin:/bin" TMPDIR="$L/tmp" TMP="$L/tmp" TEMP="$L/tmp" XDG_CACHE_HOME="$L/cache" MALLOC_ARENA_MAX=2
export LEAN_PATH="$PWD"
for d in "$PK"/*; do LEAN_PATH="$LEAN_PATH:$d/.lake/build/lib/lean"; done
