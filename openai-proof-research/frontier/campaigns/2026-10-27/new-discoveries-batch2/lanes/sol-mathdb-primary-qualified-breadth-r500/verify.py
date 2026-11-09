"""Independent read-only verifier; imports no producer or upstream verifier."""
import pathlib,json,hashlib,sys
O=pathlib.Path(__file__).resolve().parent; L=O.parent; I=L/'root-mathdb-abelianisation-retirement-intake-r499'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch {p}';assert h(b)==e['sha256'],f'hash mismatch {p}'
def canon(r):return h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
def verify():
 m=j(O/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-receipt.json'];payload={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']);assert payload=={e['path'] for e in m['files']};assert len(m['files'])==len(payload)
 for e in m['files']:check(O/e['path'],e)
 for e in j(O/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 im=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 for e in j(I/'bindings.json'):
  for key in ['original','copy']:check(pathlib.Path(e[key]),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:
  p=pathlib.Path(e['path']);check(p if p.is_absolute() else C/p,e)
 # All explicitly frozen local files bind directly to corresponding originals.
 for p in (O/'frozen').rglob('*'):
  if p.is_file():
   rel=p.relative_to(O/'frozen');root=L if rel.parts[0].startswith('root-') else L.parent.parent
   original=(L/rel) if (L/rel).is_file() else L.parent/rel.name
   assert original.is_file(),str(original);assert original.read_bytes()==p.read_bytes(),str(p)
 assignment=j(I/'reserved-ids.json');ids=assignment['ids'];queue=j(I/'queue.json');cov=j(I/'coverage-delta.json');assert len(cov)==3683
 assert len(ids)==len(set(ids))==50;assert set(ids)=={q['mathdb_id'] for q in queue};assert assignment['lane']==O.name
 assert assignment['other_active_reservations']==[];assert set(assignment['active_hypothesis_ids'])=={338290,337963};assert not set(ids)&{338290,337963,372627,372628,368940,404067,364119,339564};assert not set(map(str,ids))&set(cov)
 ds=j(O/'dispositions.json');assert len(ds)==50 and {d['ID'] for d in ds}==set(ids)
 if '--negative-test' in sys.argv:ds[0]['literal']+=' DELIBERATE MISMATCH'
 selected={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r.get('mathdb_id') in set(ids):
    assert r['mathdb_id'] not in selected;selected[r['mathdb_id']]=(str(p.resolve()),n,r)
 assert len(selected)==50
 for d in ds:
  p,n,r=selected[d['ID']];assert d['chunk']==p and d['line']==n;assert d['literal']==r['statement'],'literal mismatch'
  assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==canon(r);assert d['accepted_credit']==0
 for r in j(O/'assigned-records.json'):
  p,n,record=selected[r['record']['mathdb_id']];assert r['record']==record and r['chunk']==p and r['line']==n
 for s in j(O/'source-provenance.json'):
  if s.get('status')!='failure':
   for key in ['pdf','text']:check(O/s[key],{'size':s[key+'_size'],'sha256':s[key+'_sha256']})
 assert j(O/'proposals.json')==[];assert j(O/'coverage.json')['counts']=={'additional':9,'total':39,'next':40}
 assert j(O/'adjudications-carried.json')==j(I/'adjudications.json');assert j(O/'adjudications-carried.json')['339564']['disposition']=='RETIRE_PUBLICLY_RESOLVED'
 return {'integrity':'PASS','mathematical_acceptance':'NOT ESTABLISHED','novelty':'HOLD','records':50,'original_chunks':20,'frozen_inputs':8,'other_active_breadth_reservations':0,'payload_files':len(payload)}
try:print(json.dumps(verify(),sort_keys=True))
except Exception as e:print(json.dumps({'integrity':'FAIL','error':str(e)},sort_keys=True));sys.exit(1)
