#!/usr/bin/env bash
# fetch.sh <outfile-basename> <url> : single GET, generic UA, no retry; writes body + receipt into downloads/<dir>
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"; out="$LANE/downloads/$1"; url="$2"
code=$(timeout 60 curl -sS -L --max-time 50 -A "research-review-script/1.0" -o "$out" -w '%{http_code}' "$url")
rc=$?
python3 -I - "$out" "$url" "$code" "$rc" <<'PY'
import sys, json, hashlib, datetime, os
out, url, code, rc = sys.argv[1:]
b = open(out,'rb').read() if os.path.exists(out) else b''
json.dump(dict(url=url, utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), http_status=code, curl_rc=int(rc),
               bytes=len(b), sha256=hashlib.sha256(b).hexdigest()), open(out + '.receipt.json','w'), indent=1)
print(code, len(b), url)
PY
