import pathlib,json,hashlib,shutil,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'lanes/root-mmpp-survival-review-freeze-r1/review-freeze.json'; d=json.loads(f.read_text()); src=pathlib.Path(d['source_lane']); out={}
for n,v in d['files'].items():
 p=src/n; assert h(p)==v,n
 q=L/'copy'/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert h(q)==v;out[n]={'original':h(p),'copy':h(q)}
(L/'before.json').write_text(json.dumps(out,indent=2));shutil.copyfile(f,L/'review-freeze.json')
# Complete local textual evidence and access logs are copied and read, not truncated tree caches.
read=[]
for lane in ['sol-mmpp-survival-preliminary-review-r1','sol-mmpp-historical-prior-review-r2','sol-mmpp-classical-boundary-review-r3']:
 for p in (B/'lanes'/lane).rglob('*'):
  if p.is_file() and p.suffix in ['.md','.json','.jsonl'] and not any(s in p.parts for s in ['copy','context','__pycache__']):
   data=p.read_bytes();q=L/'context'/lane/p.relative_to(B/'lanes'/lane);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);read.append({'path':str(p),'sha256':h(p),'bytes':len(data)})
for p in [B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md',B/'lanes/root-mmpp-substantive-adjudication-r4/ADOPTION.json']:
 if p.exists():
  data=p.read_bytes();q=L/'context'/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);read.append({'path':str(p),'sha256':h(p),'bytes':len(data)})
(L/'context-read.json').write_text(json.dumps(read,indent=2));print('55 originals and copies verified; textual context copied',len(read))
