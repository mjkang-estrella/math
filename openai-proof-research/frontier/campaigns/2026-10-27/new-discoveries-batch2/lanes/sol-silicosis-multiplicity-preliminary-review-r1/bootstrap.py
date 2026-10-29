import hashlib,json,shutil,datetime
from pathlib import Path
B=Path(__file__).resolve().parents[2]; O=Path(__file__).resolve().parent
f=B/'lanes/root-silicosis-review-freeze-r1/review-freeze.json'; m=json.loads(f.read_text()); s=Path(m['source_lane']); records=[]
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as g:
  for b in iter(lambda:g.read(65536),b''):h.update(b)
 return h.hexdigest()
for n,h in m['files'].items():
 p=s/n; before=digest(p); assert before==h,(n,before,h)
 q=O/'frozen'/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 after=digest(p); copied=digest(q);assert before==after==copied
 records.append(dict(path=n,expected=h,before=before,after=after,copy=copied))
(O/'freeze-before.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=digest(f),files=records),indent=2))
for name in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
 shutil.copyfile(B/name,O/('context-'+name))
print('validated/copied',len(records))
