# usage: fetch.py OUTDIR NAME URL [NAME URL ...]; single attempt per URL, no retries
import sys, subprocess, hashlib, json, datetime, os
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
rec = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'receipts', 'http-receipts.jsonl')
a = sys.argv[2:]
for name, url in zip(a[0::2], a[1::2]):
    body = os.path.join(out, name + '.body'); hdr = os.path.join(out, name + '.hdr')
    utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    r = subprocess.run(['curl', '-sS', '-L', '--max-redirs', '5', '--max-time', '60', '--max-filesize', '40000000',
        '-A', 'Mozilla/5.0 (research-review; single-fetch)', '-D', hdr, '-o', body,
        '-w', '%{http_code} %{url_effective} %{content_type}', url], capture_output=True, text=True, timeout=90)
    parts = (r.stdout or '').split(' ', 2)
    h = hashlib.sha256(open(body, 'rb').read()).hexdigest() if os.path.exists(body) else None
    sz = os.path.getsize(body) if os.path.exists(body) else 0
    e = {"utc": utc, "url": url, "status": parts[0] if parts else None, "final_url": parts[1] if len(parts) > 1 else None,
         "content_type": parts[2] if len(parts) > 2 else None, "file": os.path.relpath(body, os.path.dirname(rec) + '/..'),
         "bytes": sz, "sha256": h, "curl_rc": r.returncode, "curl_err": r.stderr.strip()[:300]}
    open(rec, 'a').write(json.dumps(e) + '\n')
    print(e["status"], sz, e["content_type"], url)
