exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('bind(I/')[0])
refs=load(O/'flat-bindings.json'); known={x['path'] for x in refs}
f=load(L/'sol-mathdb-primary-qualified-breadth-r714/flat-bindings.json')
# Only bind flat reference paths; no recursive traversal.
for x in f:
 p=pathlib.Path(x['path'])
 if p.exists() and str(p) not in known:
  assert h(p)==x['sha256']; assert p.stat().st_size==x.get('size',x.get('bytes'))
  refs.append({'path':str(p),'sha256':h(p),'size':p.stat().st_size});known.add(str(p))
dump('flat-bindings.json',refs)
ids=set(load(I/'reserved-ids-r718.json')['ids']);rows=[]
for x in load(R/'manifest.json')['files']:
 if not x['path'].startswith('corpus/'):continue
 p=R/x['path']
 for no,line in enumerate(p.open(),1):
  r=json.loads(line);i=r.get('id',r.get('mathdb_id'))
  if i in ids:
   rows.append({'id':i,'chunk':str(p),'line':no,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
dump('literal-records.json',rows)
for r in rows:print(json.dumps(r,ensure_ascii=False))
print('CONTEXT')
for n in ['adjudications.json','hypothesis-queue.json']:print(n,(I/n).read_text())
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 print('CONTEXT',p.name,p.read_text()[:18000])
print('r363 refs',[x['path'] for x in refs if 'r363' in x['path']])
