"""Independent read-only verification; synthetic faults never mutate files."""
import json,pathlib,hashlib,sys,collections
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r717';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check_file(p,d):
 b=p.read_bytes();assert len(b)==d.get('size',d.get('bytes')),('size',str(p));assert sha(b)==d['sha256'],('hash',str(p))
def canonical(r):return sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
def verify(fault=None):
 m=load(O/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 names={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}; expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
 # Receipt may be absent on first finalization run.
 expected.discard('final-verification-receipt.json') if not (O/'final-verification-receipt.json').exists() else None
 if fault=='extra':names.add('synthetic-unlisted-payload')
 assert names==expected,('exact_payload',names^expected)
 for j,d in enumerate(m['files']):
  b=(O/d['path']).read_bytes();size=len(b)
  if j==0 and fault=='size':size+=1
  if j==0 and fault=='hash':b=(bytes([b[0]^1])+b[1:]) if b else b'x'
  assert size==d['size'],('size',d['path']);assert sha(b)==d['sha256'],('hash',d['path'])
 refs=load(O/'flat-bindings.json');assert len({x['path'] for x in refs})==len(refs)
 for x in refs:check_file(pathlib.Path(x['path']),x)
 bound={x['path']:x for x in refs}
 for p in [I/'manifest.json',I/'queue-r718.json',I/'reserved-ids-r718.json',I/'coverage-delta.json',I/'adjudications.json',I/'hypothesis-queue.json',I/'verification-receipt.json',I/'bindings.json',R/'manifest.json']:
  assert str(p) in bound
 im=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in im['files']}|set(im['excluded_exact_paths'])
 for x in im['files']:check_file(I/x['path'],x)
 pairs=load(I/'bindings.json')
 for x in pairs:
  for k in ['original','copy']:check_file(pathlib.Path(x[k]),x)
 # The original inventory manifest itself is anchored by an intake original/copy pair.
 anchor=next(x for x in pairs if x['original']==str(R/'manifest.json'));check_file(R/'manifest.json',anchor)
 rm=load(R/'manifest.json');chunks=[x for x in rm['files'] if x['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for x in chunks+rm['frozen_inputs']:check_file(R/x['path'],x)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/name).read_bytes()==(R/'frozen'/name).read_bytes()
 cov=load(I/'coverage-delta.json');assert len(cov)==8833
 q=load(I/'queue-r718.json');res=load(I/'reserved-ids-r718.json');act=load(I/'active-breadth-reservations.json')
 assert len(q)==50 and len(res['ids'])==len(set(res['ids']))==50
 ids=set(res['ids']);assert ids=={x['mathdb_id'] for x in q}
 assert res['coverage_baseline']==8833 and not res['active_hypothesis_ids']
 assert len(act)==3;sets=[set(x['ids']) for x in act];assert ids in sets
 for j,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,cov))
  assert not s&set(res['protected_ids'])
  for t in sets[:j]:assert not s&t
  assert not act[j]['active_hypothesis_ids']
 records=load(O/'literal-records.json');dis=load(O/'dispositions.json');assert len(records)==len(dis)==50
 assert {x['id'] for x in records}=={x['mathdb_id'] for x in dis}==ids
 by={x['id']:x for x in records};db={x['mathdb_id']:x for x in dis};found={}
 # Read original chunk lines, checking only assigned objects; no scientific display of neighbors.
 for x in chunks:
  p=R/x['path']
  for no,line in enumerate(p.open(),1):
   r=json.loads(line);i=r.get('mathdb_id')
   if i in ids:
    assert i not in found;found[i]=(p,no,r)
 assert set(found)==ids
 for i,(p,no,r) in found.items():
  x=by[i];d=db[i];assert x['record']==r and x['chunk']==str(p) and x['line']==no
  assert x['canonical_record_sha256']==d['canonical_record_sha256']==canonical(r)
  assert d['literal_statement_utf8']==r['statement']
  assert d['statement_utf8_sha256']==sha(r['statement'].encode())
  assert d['corpus_chunk']==str(p) and d['corpus_line']==no
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  for k in ['classification_reason','quantifier_scope','technical_assessment','disposition']:assert d[k]
  assert d['credit']==0 and not d['promotion'] and d['evidence']['literal_record_read']
 assert len(load(O/'proposals.json'))==0
 for x in load(O/'source-provenance.json'):
  for k in ['original','derivative']:check_file(pathlib.Path(x[k]['path']),x[k])
  assert x['url'].startswith('https://arxiv.org/html/') and x['url'].endswith('v1')
 assert len(load(O/'source-provenance.json'))==5
 c=load(O/'bounded-calculations.json');t=c['t'];n=5*t-10
 D=set(range(t-4,t-2))|set(range(t+1,(3*t-9)//2+1))|{(3*t-5)//2,2*t-4};assert sorted(D)==c['distance_set']
 S=D|{n-x for x in D};A=[{(v+s)%n for s in S} for v in range(n)]
 assert all(not(A[u]&A[v]) for u in range(n) for v in A[u])
 assert set(c['edge_addition_common_neighbor_witnesses'])=={str(v) for v in range(1,n) if v not in A[0]}
 for v,w in c['edge_addition_common_neighbor_witnesses'].items():assert w in A[0]&A[int(v)]
 return {'status':'INTEGRITY_PASS_ONLY','intake_direct_pairs':len(pairs),'original_chunks':20,'frozen_inputs':8,'baseline':8833,'reservations':3,'all_disjoint':True,'exact_literal_reviews':50,'classifications':dict(collections.Counter(x['classification'] for x in dis)),'proposals':0,'flat_original_bindings':len(refs),'scientific_or_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(verify(sys.argv[1] if len(sys.argv)>1 else None),sort_keys=True))
 except Exception as e:print('VERIFY_REJECT: '+repr(e),file=sys.stderr);sys.exit(1)
