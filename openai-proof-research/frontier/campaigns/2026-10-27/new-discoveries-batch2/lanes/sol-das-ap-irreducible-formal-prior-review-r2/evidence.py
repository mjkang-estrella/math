from pathlib import Path
import json,hashlib,urllib.request,urllib.parse,datetime
B=Path(__file__).resolve().parent;E=B/'extracted';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
refs=[]
for r in json.loads((E/'freeze.json').read_text())['scientific']:
 assert sha(Path(r['original']))==sha(E/r['copy'])==r['sha256'];refs.append(r)
P=B.parent/'sol-das-ap-irreducible-preliminary-review-r1'
for r in json.loads((B/'prior/freeze.json').read_text())['scientific']:
 if any(s in r['copy'] for s in ['1806.09641','2412.06379','isical-2892','iitg-thesis','http.jsonl']):
  assert sha(Path(r['original']))==sha(P/r['copy'])==r['sha256']
  refs.append(dict(original=r['original'],copy=str(P/r['copy']),sha256=r['sha256']))
(B/'immutable-references.json').write_text(json.dumps(refs,indent=2))
out=B/'retrieval';out.mkdir(exist_ok=True)
urls=[('crossref-title.json','https://api.crossref.org/works?query.title=Sign%20patterns%20that%20allow%20algebraic%20positivity&rows=3'),('openalex-title.json','https://api.openalex.org/works?search=Sign%20patterns%20that%20allow%20algebraic%20positivity&per-page=3')]
for name,url in urls:
 row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'IndependentSourceReview/1.0'}),timeout=30) as r:
   raw=r.read(3000000);row.update(status=r.status,final_url=r.url)
  p=out/name;p.write_bytes(raw);f=out/('frozen-'+name);f.write_bytes(raw)
  assert sha(p)==sha(f);row.update(file=str(p),frozen=str(f),sha256=sha(p),bytes=len(raw))
 except Exception as e:row.update(error=repr(e))
 with (out/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(row)
