import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parent;I=L.parent/'root-mathdb-breadth-intake-r685'
q=json.loads((I/'queue-r686.json').read_text());ids={r['mathdb_id'] for r in q}; out=[]
for p in sorted((L.parent/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:out.append({'chunk':str(p),'line':n,'record':r,'canonical_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(L/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for r in out:print(json.dumps(r,ensure_ascii=False))
for name in ['active-breadth-reservations.json','coverage-delta.json','adjudications.json']:
 v=json.loads((I/name).read_text()); print(name, str(v)[:6500] if name!='coverage-delta.json' else ('keys '+str(v.keys())))
