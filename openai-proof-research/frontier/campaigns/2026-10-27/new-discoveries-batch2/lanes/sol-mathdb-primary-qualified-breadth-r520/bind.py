import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r519';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sig(p):
 b=p.read_bytes();return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):assert sig(p)=={'size':e.get('size',e.get('bytes')),'sha256':e['sha256']},str(p)
def write(n,a):(P/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
flat=j(P/'initial-bindings.json')
for s,e in flat.items():check(pathlib.Path(s),e)
m=j(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};assert actual-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:check(I/e['path'],e)
pairs=j(I/'bindings.json')
for e in pairs:
 for key in ['original','copy']:
  p=pathlib.Path(e[key]);check(p,e);flat[str(p)]=sig(p)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:
 p=C/e['path'];check(p,e);flat[str(p)]=sig(p)
refs=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-cayley-review-intake-r363/disposition.json']
for p in refs:flat[str(p)]=sig(p)
write('flat-bindings.json',flat)
cov=j(I/'coverage-delta.json');assert len(cov)==4083
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
q=j(I/'queue-r520.json');ids={r['mathdb_id'] for r in q};assert len(q)==len(ids)==50 and ids==set(j(I/'reserved-ids-r520.json')['ids'])
route=[json.loads(s) for s in (I/'routing-queue.jsonl').open()];assert len(route)==6000
assert (I/'routing-queue.jsonl').read_bytes()==(I/'frozen/root-mathdb-breadth-intake-r517/routing-queue.jsonl').read_bytes()
assert all(r in route for r in q)
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50;rows.sort(key=lambda r:r['mathdb_id']);write('assigned-records.json',rows)
write('initial-verification.json',{'integrity':'PASS','pairs':len(pairs),'chunks':20,'frozen_inputs':8,'baseline':4083,'reserved_sets':3,'routing_rows':6000,'records':50})
print('PASS',len(flat),'bindings');print('record keys',rows[0]['record'].keys())
for r in rows[:25]:print('\nID',r['mathdb_id'],'\n',r['statement'],'\nSOURCE',r['record'].get('references',r['record'].get('source')))
