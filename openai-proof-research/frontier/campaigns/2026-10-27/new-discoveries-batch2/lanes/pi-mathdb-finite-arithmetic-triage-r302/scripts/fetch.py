"""Bounded, resumable MathDB fetcher for lane r302.
Usage: python3 -I fetch.py <mode> <args...>
Modes:
  list <tag|all> <offset> <outfile>   one list page (limit=100)
  detail <number> <outfile>           one record detail
Writes JSON; never retries on 403/429/challenge; exits 3 on stop condition.
"""
import json, sys, time, urllib.request, urllib.error

BASE = "https://mathdb.com/api/posts"
HDRS = {"User-Agent": "openai-proof-research-r302-triage/0.1 (read-only; bounded)"}

def get(url):
    req = urllib.request.Request(url, headers=HDRS)
    try:
        with urllib.request.urlopen(req, timeout=45) as r:
            return r.status, r.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()[:2000]

def main():
    mode = sys.argv[1]
    if mode == "list":
        tag, off, out = sys.argv[2], int(sys.argv[3]), sys.argv[4]
        url = f"{BASE}?limit=100&offset={off}" + (f"&tag={tag}" if tag != "all" else "")
    elif mode == "detail":
        num, out = sys.argv[2], sys.argv[3]
        url = f"{BASE}/{num}"
    else:
        sys.exit("bad mode")
    st, body = get(url)
    if st == 200:
        try:
            d = json.loads(body)
        except Exception:
            sys.exit(3)
        json.dump({"url": url, "retrieved_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "data": d},
                  open(out, "w"), indent=1, ensure_ascii=False)
        print("OK", url, len(body))
    else:
        print("HTTP", st, url, body[:200].decode("utf-8", "replace"))
        sys.exit(3 if st in (403, 429) else 4)

if __name__ == "__main__":
    main()
