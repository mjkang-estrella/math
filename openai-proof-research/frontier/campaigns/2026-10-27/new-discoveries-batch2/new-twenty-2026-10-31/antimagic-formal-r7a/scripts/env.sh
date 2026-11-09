LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
TOOLS=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export PATH="$LANE/scripts/bin:$TOOLS:$PATH"
PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build"
for p in "$PACKAGES"/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$p"; done
export LEAN_PATH
