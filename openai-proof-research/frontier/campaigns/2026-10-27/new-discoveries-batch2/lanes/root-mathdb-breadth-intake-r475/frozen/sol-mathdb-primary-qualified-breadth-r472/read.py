import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r471';V=B/'pi-mathdb-full-corpus-inventory-r301'
for name in ['reserved-ids.json','coverage-delta.json']:
 d=json.loads((I/name).read_text());print(name, str(d)[:3500])
for p in [B/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json',B/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json',B/'root-mathdb-cayley-review-intake-r363'/'disposition.json']:
 d=json.loads(p.read_text());print(p.name,str(d)[:2200])
ids={r['mathdb_id'] for r in json.loads((I/'queue.json').read_text())};out=[]
for p in sorted((V/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('id',r.get('mathdb_id')) in ids:
   out.append({'record':r,'chunk':str(p),'line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50,len(out)
(L/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for e in out:print(json.dumps(e,ensure_ascii=False))
