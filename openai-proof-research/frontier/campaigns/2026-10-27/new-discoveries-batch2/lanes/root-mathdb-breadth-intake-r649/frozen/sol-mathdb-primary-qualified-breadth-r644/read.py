import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r643';B=L.parent
load=lambda p:json.loads(p.read_text())
f=load(L/'sol-mathdb-primary-qualified-breadth-r642/flat-bindings.json'); initial=load(P/'initial-bindings.json')
selected=[x for x in f if any(t in x['path'] for t in ['root-mathdb-accepted-exclusions-r304/','r363/','ledger.json','prior-campaign-context.json'])]
for p in [B/'ledger.json',B/'prior-campaign-context.json']:
 if not any(x['path']==str(p) for x in selected):
  b=p.read_bytes();selected.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
for x in selected:
 b=pathlib.Path(x['path']).read_bytes();assert len(b)==x['size'] and hashlib.sha256(b).hexdigest()==x['sha256']
(P/'flat-bindings.json').write_text(json.dumps(initial+selected,indent=2)+'\n')
print('context',[(x['path'],x['sha256']) for x in selected])
for x in selected:
 if any(t in x['path'] for t in ['DECISION','ledger.json','prior-campaign-context','accepted-exclusions.json','historical-dispositions.json']):
  d=load(pathlib.Path(x['path'])) if x['path'].endswith('.json') else pathlib.Path(x['path']).read_text();print('CONTEXT',x['path'],str(d)[:2800])
print('ADJ', (I/'adjudications.json').read_text());print('HYP',(I/'hypothesis-queue.json').read_text())
q=load(I/'queue-r644.json');ids={x['mathdb_id'] for x in q};c=load(I/'coverage-delta.json');assert len(c)==7033
sets=load(I/'active-breadth-reservations.json');seen=set()
for s in sets:
 a=set(s['ids']);assert len(a)==50 and not a&seen and not a&set(map(int,c)) and not a&set(s['protected_ids']);seen|=a
assert ids==set(load(I/'reserved-ids-r644.json')['ids'])
rows=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:
   rows.append(dict(record=r,chunk=str(p),line=n,canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
assert len(rows)==50
(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for x in rows: print('RECORD',json.dumps(x,ensure_ascii=False))
