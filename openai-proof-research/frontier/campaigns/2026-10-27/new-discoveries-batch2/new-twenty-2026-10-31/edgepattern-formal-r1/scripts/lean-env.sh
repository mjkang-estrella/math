export LEAN_BIN=${LEAN_BIN:-/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean}
export LEAN_PACKAGES=${LEAN_PACKAGES:-/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages}
export LEAN_PATH="$PWD/formal"
for package in "$LEAN_PACKAGES"/*; do
  if [ -d "$package/.lake/build/lib/lean" ]; then export LEAN_PATH="$LEAN_PATH:$package/.lake/build/lib/lean"; fi
done
export MALLOC_ARENA_MAX=2
