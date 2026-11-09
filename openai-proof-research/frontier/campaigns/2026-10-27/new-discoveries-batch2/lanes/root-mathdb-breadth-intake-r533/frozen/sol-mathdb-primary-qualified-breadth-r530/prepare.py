import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent;B=L.parent;I=L/'root-mathdb-ordinal-exclusion-intake-r529';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
refs=j(D/'flat-bindings.json')
def bind(p,e=None):
 p=p.resolve();b=p.read_bytes();s={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if e:assert s['size']==e.get('size',e.get('bytes')) and s['sha256']==e['sha256'],str(p)
 refs[str(p)]=s
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for e in j(L/'sol-mathdb-ordinal-balls-preliminary-review-r526'/'flatbindings.json'):bind(pathlib.Path(e['path']),e)
for p in [B/'ledger.json',B/'prior-campaign-context.json']:
 if p.exists():bind(p)
for p in L.glob('*r304/*.json'):
 if p.name in ['accepted-exclusions.json','historical-dispositions.json']:bind(p)
for p in L.glob('*r363/*'):
 if p.is_file() and p.suffix in ['.md','.json']:bind(p)
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
cov=j(I/'coverage-delta.json');assert len(cov)==4233
active=j(I/'active-breadth-reservations.json');assert len(active)==2
seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
res=j(I/'reserved-ids.json');ids=set(res['ids']);assert len(ids)==50 and {r['mathdb_id'] for r in j(I/'queue.json')}==ids
rows=[]
for e in chunks:
 p=C/e['path']
 for ln,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'corpus_path':str(p),'line':ln,'record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
(D/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('VERIFIED 20 original chunks + 8 frozen inputs; two disjoint reservations; flat refs',len(refs))
print('record keys',list(rows[0]['record']))
for r in rows:print('\nID',r['mathdb_id'],json.dumps(r['record'],ensure_ascii=False))
print('CONTEXT FILES',*[p for p in refs if 'r304/' in p or 'r363/' in p],sep='\n')
