LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build"
for pkg in "$PACKAGES"/*; do export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; done
export PATH="${LEAN%/lean}:$PATH"
