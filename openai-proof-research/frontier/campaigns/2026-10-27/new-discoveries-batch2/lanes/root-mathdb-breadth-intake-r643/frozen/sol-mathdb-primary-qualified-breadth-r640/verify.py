"""Independent read-only verification. Invoke only via verify.sh (fixed resource guard)."""
import pathlib,json,hashlib,sys,itertools
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r639';V=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(d):return hashlib.sha256(d).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,x):
 d=p.read_bytes();assert len(d)==x.get('size',x.get('bytes')),f'size mismatch: {p}';assert sha(d)==x['sha256'],f'hash mismatch: {p}'
def run():
 m=load(O/'manifest.json');excluded={'manifest.json','final-verification-receipt.json'};assert set(m['excluded_exact_paths'])==excluded
 entries={x['path']:x for x in m['files']};assert len(entries)==len(m['files'])
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()};assert all(not p.is_symlink() for p in O.rglob('*'))
 neg=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 if neg=='extra':actual.add('injected-extra-file')
 assert actual-set(excluded)==set(entries),'extra/missing payload file'
 for n,x in entries.items():
  d=(O/n).read_bytes()
  if n==sorted(entries)[0]:
   if neg=='hash':d=bytes([d[0]^1])+d[1:]
   if neg=='size':d=d+b'!'
  assert len(d)==x['size'],f'payload size mismatch: {n}'
  assert sha(d)==x['sha256'],f'payload hash mismatch: {n}'
 refs=load(O/'flat-bindings.json')+load(O/'source-bindings.json')
 for x in refs:check(pathlib.Path(x['path']),x)
 # Current exact intake files, not an upstream verifier or historical recursive expansion.
 im=load(I/'manifest.json');check(I/'manifest.json',{'sha256':'c37c968e58ba27a51e2a0c673112f3b661cd7dc6e993d7590694ee209f017498','size':9089})
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={x['path'] for x in im['files']}|set(im['excluded_exact_paths'])
 for x in im['files']:check(I/x['path'],x)
 for x in load(I/'bindings.json'):
  check(pathlib.Path(x['original']),x);check(pathlib.Path(x['copy']),x)
 vm=load(V/'manifest.json');check(V/'manifest.json',{'sha256':'4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15','size':22047})
 chunks=[x for x in vm['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(vm['frozen_inputs'])==8
 for x in chunks+vm['frozen_inputs']:check(V/x['path'],x)
 q=load(I/'queue-r640.json');reserved=load(I/'reserved-ids-r640.json');ids={x['mathdb_id'] for x in q};assert len(q)==len(ids)==50 and ids==set(reserved['ids']);assert reserved['coverage_baseline']==6883 and reserved['lane']==O.name
 cov=load(I/'coverage-delta.json');assert len(cov)==6883
 active=load(I/'active-breadth-reservations.json');assert len(active)==3;sets=[set(x['ids']) for x in active]
 assert all(len(s)==50 and not s&set(map(int,cov)) and not s&set(a['protected_ids']) for s,a in zip(sets,active));assert all(not s&t for s,t in itertools.combinations(sets,2));assert sets[2]==ids
 literal=load(O/'literal-records.json');dis=load(O/'dispositions.json');assert len(literal)==len(dis)==50;assert {x['mathdb_id'] for x in dis}==ids
 found={}
 for x in chunks:
  p=V/x['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(p),n,r)
 assert len(found)==50
 for a,d in zip(literal,dis):
  r=a['record'];id=r['mathdb_id'];p,n,orig=found[id];assert r==orig and a['chunk']==p and a['line']==n
  canonical=sha(json.dumps(orig,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert canonical==a['canonical_record_sha256']==d['canonical_record_sha256'];assert d['mathdb_id']==id and d['chunk']==p and d['line']==n
  assert d['exact_utf8_statement']==orig['statement'] and d['statement_utf8_sha256']==sha(orig['statement'].encode())
  assert d['scope_category'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['quantifiers'] and d['technical_review'] and d['accepted_credit']==0
 assert len(load(O/'proposals.json'))==0
 for x in load(O/'selected-passages.json'):
  assert pathlib.Path(x['source']).read_text()[x['char_start']:x['char_end']]==x['text'],'selected passage mismatch'
 print(json.dumps({'integrity':'PASS','literal_records':50,'corpus_chunks_in_place':20,'frozen_inputs_in_place':8,'original_copy_pairs':len(load(I/'bindings.json')),'baseline_literal_reviews':6883,'three_disjoint_reservations':True,'bound_references_checked':len(refs),'math_novelty_acceptance':'NOT ESTABLISHED','proposals':0}))
if __name__=='__main__':
 try:run()
 except Exception as e:print('VERIFY FAIL: '+str(e),file=sys.stderr);sys.exit(1)
