import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=L.parent/'sol-floor-sums-breadth-depth-r241'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
paths=list(p for p in R.iterdir() if p.is_file())
paths += [p for p in (R/'sources').iterdir() if p.is_file() and ('wong' in p.name or 'floor' in p.name)]
paths += [p for p in (R/'frozen').rglob('*wong*') if p.is_file()]
for p in paths:
 q=L/'frozen'/p.relative_to(R);q.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);q.write_bytes(p.read_bytes());assert sha(q)==h==sha(p)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,size=p.stat().st_size))
(L/'bindings.json').write_text(json.dumps({'frozen_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2))
admin=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']
admin += [B.parents[3]/'sources'/'upstream.json',B.parents[3]/'sources'/'CONTENTS.md']
for p in admin:
 if p.exists():
  q=L/'administrative'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
print(json.dumps({'frozen_files':len(rows),'names':[r['copy'] for r in rows]}))
