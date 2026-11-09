import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent
names=['root-mathdb-breadth-intake-r459','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']
bind={}; checks=[]
def J(p):return json.loads(p.read_text())
def freeze(p,sha=None,size=None):
 p=p.resolve(); data=p.read_bytes(); h=hashlib.sha256(data).hexdigest()
 assert sha is None or sha==h, str(p)+' HASH'
 assert size is None or size==len(data), str(p)+' SIZE'
 bind[str(p)]={'path':str(p),'sha256':h,'bytes':len(data)}
for name in names:
 d=B/name; freeze(d/'manifest.json'); m=J(d/'manifest.json'); files=m if isinstance(m,list) else m['files']
 for f in files:freeze(d/f['path'],f['sha256'],f.get('size',f.get('bytes')))
 if name=='pi-mathdb-full-corpus-inventory-r301':
  frozen=m['frozen_inputs']; assert {x['path'] for x in frozen}=={str(p.relative_to(d)) for p in (d/'frozen').rglob('*') if p.is_file()}
  for f in frozen:freeze(d/f['path'],f['sha256'],f['bytes'])
  chunks=[f for f in files if f['path'].startswith('corpus/')]; assert len(chunks)==20
  (L/'inventory-frozen-membership.json').write_text(json.dumps(frozen,indent=2)+'\n')
 else:
  if (d/'bindings.json').exists():
   freeze(d/'bindings.json')
   for f in J(d/'bindings.json'):
    freeze(pathlib.Path(f['original']),f['sha256'],f.get('size',f.get('bytes')))
    cp=pathlib.Path(f.get('copy',f.get('frozen','')))
    if str(cp)!='.':freeze(cp if cp.is_absolute() else d/cp,f['sha256'],f.get('size',f.get('bytes')))
 checks.append(name)
r=J(B/names[0]/'reserved-ids.json');q=J(B/names[0]/'queue.json');cov=J(B/names[0]/'coverage-delta.json');ids=set(r['ids'])
assert len(ids)==50 and ids=={x['mathdb_id'] for x in q}
assert r['lane']==L.name and not ids.intersection(r['other_active_reservations'])
assert len(cov)==2883 and not ids.intersection(map(int,cov))
assert not ids.intersection([372627,372628,368940,404067,364119])
(L/'bindings.json').write_text(json.dumps(list(bind.values()),indent=2)+'\n')
(L/'preflight.json').write_text(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifests':checks,'flat_references':len(bind),'chunks':20,'assignment':50,'baseline_statement_reviews':len(cov),'upstream_code_executed':False},indent=2)+'\n')
print('PASS',len(bind),'flat bindings; 20 chunks; 50 assigned; baseline',len(cov))
