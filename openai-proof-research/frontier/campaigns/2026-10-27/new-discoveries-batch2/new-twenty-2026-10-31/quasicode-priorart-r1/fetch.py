import os, sys, json, hashlib, datetime, urllib.request, urllib.error
from pathlib import Path
BASE=Path(__file__).resolve().parent
os.environ['TMPDIR']=str(BASE/'tmp')
for d in ('tmp','receipts','bodies'): (BASE/d).mkdir(exist_ok=True)
name,url=sys.argv[1:3]
assert not any(s in url.lower() for s in ('sciencedirect','elsevier','worldscientific','api.crossref','semanticscholar','export.arxiv'))
out=BASE/'receipts'/name
assert not out.exists()
rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
    req=urllib.request.Request(url,headers={'User-Agent':'Math-prior-art-research/1.0'})
    with urllib.request.urlopen(req,timeout=35) as r:
        data=r.read(25000000); rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
except urllib.error.HTTPError as e:
    data=e.read();rec.update(status=e.code,error=str(e))
except Exception as e:
    data=b'';rec.update(status=None,error=str(e))
out.write_bytes(data)
rec['sha256']=hashlib.sha256(data).hexdigest();rec['bytes']=len(data)
out.with_name(name+'.receipt.json').write_text(json.dumps(rec,indent=2))
print(json.dumps(rec))
