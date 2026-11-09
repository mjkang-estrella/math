ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin
export LEAN_PATH="$PWD"
for p in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/*; do LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
