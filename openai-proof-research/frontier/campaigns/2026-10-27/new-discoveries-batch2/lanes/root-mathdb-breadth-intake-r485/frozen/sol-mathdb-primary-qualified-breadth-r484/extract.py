import json,pathlib,hashlib
W=pathlib.Path(__file__).resolve().parent; L=W.parent;I=W/'frozen/root-mathdb-circulant-13-prior-adjudication-r481';ids=set(json.loads((I/'reserved-ids-r484.json').read_text())['ids']);out=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:out.append({'record':r,'original_chunk':str(p),'original_line':n})
assert len(out)==50
(W/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out[0],ensure_ascii=False,indent=2))
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 x=json.loads((W/'frozen/root-mathdb-accepted-exclusions-r304'/f).read_text());print(f,type(x),list(x)[:8] if isinstance(x,dict) else len(x))
