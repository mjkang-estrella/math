#!/bin/bash
set -u
L=$(cd "$(dirname "$0")/.." && pwd)
name=$1; url=$2
mkdir "$L/downloads/$name" || exit 1
printf '%s\n' "$url" > "$L/downloads/$name/url.txt"
date -u +%FT%TZ > "$L/downloads/$name/utc.txt"
curl --max-time 45 --max-filesize 20000000 -L -D "$L/downloads/$name/headers.txt" -o "$L/downloads/$name/body" -w '%{http_code}\n' "$url" > "$L/downloads/$name/status.txt" 2> "$L/downloads/$name/stderr.txt"
cat "$L/downloads/$name/status.txt"
