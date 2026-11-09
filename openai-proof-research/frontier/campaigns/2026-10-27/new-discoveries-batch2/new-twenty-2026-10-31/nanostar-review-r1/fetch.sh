#!/bin/bash
set -u
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-review-r1
name=$1; url=$2
mkdir "downloads/$name" || exit 1
curl --max-time 35 --max-filesize 16000000 --location --silent --show-error --dump-header "downloads/$name/headers" --output "downloads/$name/body" --write-out '%{http_code} %{url_effective}\n' "$url" >"downloads/$name/status" 2>"downloads/$name/error"
printf '%s\n' "$url" >"downloads/$name/url"
sha256sum "downloads/$name/body" >"downloads/$name/sha256" 2>/dev/null
cat "downloads/$name/status"
