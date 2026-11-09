#!/usr/bin/env python3
"""Provenance-safe retrieval logger for lane pi-fourprojection-source-access-r3.
Records URL, final URL, status, content-type, bytes, sha256 for every actual response.
No retries against 429; caller respects rate limits. Writes only inside this lane."""
import sys, json, hashlib, datetime, subprocess

OUT = "sources"
LOG = "sources/retrievals.json"

def load_log():
    try:
        return json.load(open(LOG))
    except Exception:
        return []

def save_log(entries):
    json.dump(entries, open(LOG, "w"), indent=1)

def fetch(name, url, headers=None, timeout=60, method="GET", extra=None):
    entries = load_log()
    if any(e["name"] == name for e in entries):
        print(f"SKIP {name}: already logged")
        return None
    cmd = ["curl", "-sS", "-L", "--max-time", str(timeout), "-A",
           "Mozilla/5.0 (X11; Linux x86_64) research-lane-source-check",
           "-w", "%{http_code}\\t%{content_type}\\t%{url_effective}",
           "-o", f"{OUT}/{name}", url]
    if headers:
        for k, v in headers.items():
            cmd += ["-H", f"{k}: {v}"]
    if method == "HEAD":
        cmd.append("-I")
    r = subprocess.run(cmd, capture_output=True, timeout=timeout + 15)
    body = open(f"{OUT}/{name}", "rb").read()
    out = r.stdout.decode("utf-8", "replace").strip().split("\n")[-1]
    parts = out.split("\t")
    status = int(parts[0]) if parts[0].isdigit() else 0
    entry = {
        "name": name, "url": url, "retrieved_utc": datetime.datetime.utcnow().isoformat() + "Z",
        "status": status,
        "content_type": parts[1] if len(parts) > 1 else "unknown",
        "final_url": parts[2] if len(parts) > 2 else url,
        "bytes": len(body),
        "sha256": hashlib.sha256(body).hexdigest(),
        "path": f"{OUT}/{name}",
    }
    if extra:
        entry.update(extra)
    if r.stderr.strip():
        entry["curl_stderr"] = r.stderr.decode("utf-8", "replace")[:500]
    entries.append(entry)
    save_log(entries)
    print(json.dumps({k: entry[k] for k in ("name", "url", "status", "content_type", "bytes", "sha256")}, indent=1))
    return entry

if __name__ == "__main__":
    spec = json.loads(sys.argv[1])
    fetch(**spec)
