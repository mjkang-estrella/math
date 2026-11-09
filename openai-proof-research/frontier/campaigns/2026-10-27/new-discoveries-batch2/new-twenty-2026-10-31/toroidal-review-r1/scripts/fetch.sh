#!/bin/bash
set -eu
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/toroidal-review-r1
export TMPDIR="$L/tmp" XDG_CACHE_HOME="$L/cache"
name=$1; url=$2
mkdir "$L/downloads/$name"
printf '%s\n' "$url" > "$L/downloads/$name/url"
date -u +%FT%TZ > "$L/downloads/$name/date"
curl --max-time 35 --location --max-redirs 3 --proto '=https' --proto-redir '=https' -A 'Independent mathematical review' -D "$L/downloads/$name/headers" -o "$L/downloads/$name/body" -w '%{http_code} %{url_effective}\n' "$url" > "$L/downloads/$name/status" 2> "$L/downloads/$name/stderr" || true
sha256sum "$L/downloads/$name/body" > "$L/downloads/$name/sha256" 2>/dev/null || true
cat "$L/downloads/$name/status"
