#!/usr/bin/env python3
"""Read-only verifier. Run through fixed helper_guard.py. No upstream code executed."""
import pathlib,json,hashlib,sys,copy
L=pathlib.Path(__file__).resolve().parent;I=L.parent/'root-mathdb-breadth-intake-r595';R=L.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(pathlib.Path(p).read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def ck(p,r):
 b=pathlib.Path(p).read_bytes();assert len(b)==r.get('size',r.get('bytes')),f'size mismatch {p}';assert h(b)==r['sha256'],f'hash mismatch {p}'
def exact(root,m,excluded):
 expected={r['path'] for r in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(excluded)
 assert actual==expected,f'exact payload mismatch: extra {actual-expected}, missing {expected-actual}'
 for r in m['files']:
  p=pathlib.Path(r['path']);assert not p.is_absolute() and '..' not in p.parts
  ck(root/p,r)
def verify():
 m=load(L/'manifest.json');mode=sys.argv[1] if len(sys.argv)>1 else None
 if mode=='--negative-hash':m['files'][0]['sha256']='0'*64
 if mode=='--negative-size':m['files'][0]['size']+=1
 if mode=='--negative-extra':m['files']=m['files'][1:]
 exact(L,m,['manifest.json','final-verification-receipt.json'])
 for r in load(L/'flat-bindings.json'):ck(r['path'],r)
 im=load(I/'manifest.json');exact(I,im,im['excluded_exact_paths'])
 for r in load(I/'bindings.json'):
  ck(r['original'],r);ck(r['copy'],r);assert pathlib.Path(r['original']).read_bytes()==pathlib.Path(r['copy']).read_bytes()
 inv=load(R/'manifest.json');chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for r in chunks+inv['frozen_inputs']:ck(R/r['path'],r)
 res=load(I/'reserved-ids.json');ids=res['ids'];assert len(ids)==len(set(ids))==50;assert res['lane']==L.name
 assert [r['mathdb_id'] for r in load(I/'queue.json')]==ids
 cov=load(I/'coverage-delta.json');assert len(cov)==5833
 sets=[set(r['ids']) for r in load(I/'active-breadth-reservations.json')];assert len(sets)==3 and set(ids) in sets
 for j,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
  for t in sets[:j]:assert not s&t
 assert set(res['other_active_reservations'])==set.union(*(s for s in sets if s!=set(ids)))
 assert not set(ids)&{337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439}
 literal=load(L/'literal-records.json');dis=load(L/'dispositions.json');assert len(literal)==len(dis)==50
 assert [x['record']['mathdb_id'] for x in literal]==[d['mathdb_id'] for d in dis]==ids
 selected={}
 for c in chunks:
  p=R/c['path']
  for line,b in enumerate(p.open(),1):
   r=json.loads(b);i=r.get('mathdb_id')
   if i in ids:
    assert i not in selected;selected[i]=(str(p),line,r)
 assert len(selected)==50
 for x,d in zip(literal,dis):
  r=x['record'];i=r['mathdb_id'];p,line,original=selected[i];assert r==original
  canon=h(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert x['canonical_record_sha256']==d['canonical_record_sha256']==canon
  assert x['corpus_path']==d['corpus_path']==p and x['line']==d['corpus_line_1based']==line
  assert d['statement']==r['statement'] and d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['scope_flags']['literal_record_read'] and not d['scope_flags']['current_registry_cleared'] and d['accepted_credit']==0
 assert len(load(L/'proposals.json'))<=3
 for r in load(L/'source-provenance.json'):
  if 'path' in r:ck(r['path'],r)
  if 'derivative' in r:ck(r['derivative']['path'],r['derivative'])
 return {'integrity':'PASS','intake_exact_payload':'PASS','direct_original_copy_pairs':len(load(I/'bindings.json')),'corpus_chunks_in_place':20,'frozen_inputs_in_place':8,'baseline_record_reviews':5833,'assigned_literal_record_reviews':50,'self_contained_flags_true':sum(d['scope_flags']['self_contained_mathematical_statement'] for d in dis),'proposals':len(load(L/'proposals.json')),'math_novelty':'NOT_CERTIFIED_HOLD'}
try:print(json.dumps(verify(),sort_keys=True))
except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
