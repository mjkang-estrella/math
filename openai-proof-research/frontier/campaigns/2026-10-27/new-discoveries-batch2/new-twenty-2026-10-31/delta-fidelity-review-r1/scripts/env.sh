lane=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
pkgs=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$lane/fresh/lean"
for d in "$pkgs"/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$d"; done
