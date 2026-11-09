"""Targeted per-record MathDB fetches for batch1 triage. Read-only public API. No retries on 403/429/challenge."""
import json, time, urllib.request, hashlib, sys, os
os.makedirs('primary', exist_ok=True)
ids=json.load(open('screen/batch1-excerpts.json'))
log=[]
for n in ids:
    url=f"https://mathdb.com/api/posts/{n}"
    try:
        req=urllib.request.Request(url, headers={"User-Agent":"openai-proof-research-scout/0.1 (read-only)"})
        with urllib.request.urlopen(req, timeout=30) as r:
            body=r.read()
        h=hashlib.sha256(body).hexdigest()
        p=f"primary/mathdb-{n}.json"
        open(p,'wb').write(body)
        d=json.loads(body)
        print(n, d.get('status'), d.get('title','')[:60], 'sha', h[:12], flush=True)
        log.append({'id':n,'url':url,'sha256':h,'bytes':len(body),'file':p,'retrieved':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
    except Exception as e:
        print(n,'FAIL',repr(e)[:120], flush=True)
        log.append({'id':n,'url':url,'error':repr(e)[:300],'retrieved':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
    time.sleep(0.7)
json.dump(log, open('artifacts/batch1-access.json','w'), indent=1)
