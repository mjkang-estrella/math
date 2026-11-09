#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
# Reuse an already downloaded, pinned binary without changing the sibling project.
for candidate in \
  "$project_dir/.tools/lean-4.34.1-linux/bin/lake" \
  "$project_dir/../dlp-research/.tools/lean-4.34.1-linux/bin/lake"; do
  if [[ -x "$candidate" ]]; then exec "$candidate" "$@"; fi
done
if command -v lake >/dev/null 2>&1; then exec lake "$@"; fi
printf '%s\n' 'Install elan (https://lean-lang.org/install/) and the version in lean-toolchain.' >&2
exit 1

