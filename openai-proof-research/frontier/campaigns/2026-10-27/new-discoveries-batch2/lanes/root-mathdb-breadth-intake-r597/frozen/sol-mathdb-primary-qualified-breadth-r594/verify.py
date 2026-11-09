"""Independent read-only verifier. Run through the fixed helper_guard.py. No upstream executable imports."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r593';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),'size mismatch '+str(p);assert sha(b)==e['sha256'],'hash mismatch '+str(p)
def exact(root,m,negative=None):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('synthetic-extra-file')
 assert actual==set(names),'extra/missing payload'
 for n,e in enumerate(m['files']):
  b=(root/e['path']).read_bytes()
  if n==0 and negative=='size':b+=b'x'
  if n==0 and negative=='hash':b=bytes([b[0]^1])+b[1:]
  assert len(b)==e.get('size',e.get('bytes')),'payload size mismatch'
  assert sha(b)==e['sha256'],'payload hash mismatch'
def verify(negative=None):
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m,negative)
 refs=j(P/'flat-bindings.json');seen={}
 for e in refs:
  if e['path'] in seen:assert seen[e['path']]==e
  seen[e['path']]=e;check(pathlib.Path(e['path']),e)
 assert seen[str(I/'manifest.json')]['sha256']=='c0e47e4e35ab9e7f4febfcb62cd1626c1ffe92e843549b95494c7a88012fb8f2'
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 cm=j(C/'manifest.json');assert sha((C/'manifest.json').read_bytes())=='4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15'
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 reservation=j(I/'reserved-ids.json');ids=set(reservation['ids']);assert len(ids)==50 and reservation['lane']==P.name
 assert {r['mathdb_id'] for r in j(I/'queue.json')}==ids
 cov=j(I/'coverage-delta.json');assert len(cov)==5783
 active=j(I/'active-breadth-reservations.json');sets=[]
 for r in active:
  s=set(r['ids']);assert len(s)==50 and not s&set(map(int,cov)) and not s&set(reservation['protected_ids'])
  for t in sets:assert not s&t
  sets.append(s)
 assert len(sets)==3 and ids in sets
 assert next(r for r in active if 'r504' in r['lane'])['status']=='rate_limited_reserved_unreviewed'
 ds=j(P/'dispositions.json');literal=j(P/'literal-records.json');assert len(ds)==len(literal)==50 and {d['mathdb_id'] for d in ds}==ids
 found={}
 for e in chunks:
  f=C/e['path']
  for n,line in enumerate(f.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(f),n,r)
 assert set(found)==ids
 for rows in [ds,literal]:
  for d in rows:
   f,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==f and d['corpus_line']==n and d['statement']==r['statement']
   assert d['statement_utf8_sha256']==sha(r['statement'].encode())
   assert d['canonical_record_sha256']==sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
   if 'record' in d:assert d['record']==r
 for d in ds:
  assert d['accepted_credit']==0 and d['scope_flags']['literal_statement_read'] and d['scope_flags']['quantifiers_read']
  assert d['complete_self_contained_statement']==d['scope_flags']['complete_self_contained_statement']
  assert not d['scope_flags']['current_registry_cleared'] and not d['scope_flags']['novelty_pass']
 assert j(P/'proposals.json')==[]
 return {'integrity':'PASS','assigned_record_reviews':50,'self_contained_literal_statements':sum(d['complete_self_contained_statement'] for d in ds),'selected_primary_passages':sum(d['scope_flags']['selected_primary_passage_read'] for d in ds),'original_chunks':20,'frozen_inputs':8,'proposals':0,'mathematics_or_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(verify(sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None),sort_keys=True))
 except (AssertionError,OSError,ValueError,KeyError) as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
