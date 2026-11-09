"""Independent read-only verifier. Run using verify.sh under the immutable guard."""
import pathlib,json,hashlib,sys,collections
O=pathlib.Path(__file__).resolve().parent
L=O.parent
I=L/'root-mathdb-breadth-intake-r675'
R=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,h,s):
 b=p.read_bytes()
 if len(b)!=s:raise ValueError('size mismatch '+str(p))
 if sha(b)!=h:raise ValueError('hash mismatch '+str(p))
def payload(root):
 m=load(root/'manifest.json')
 expected={r['path'] for r in m['files']}
 if len(expected)!=len(m['files']):raise ValueError('duplicate paths')
 exclusions=set(m['excluded_exact_paths'])
 if exclusions!={'manifest.json','final-verification-receipt.json'}:raise ValueError('wrong exclusions')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 if actual-exclusions!=expected:raise ValueError('payload path mismatch')
 for r in m['files']:
  p=root/r['path']
  if p.is_symlink() or not p.resolve().is_relative_to(root.resolve()):raise ValueError('unsafe path')
  check(p,r['sha256'],r['size'])
def verify():
 payload(O)
 check(I/'manifest.json','a24c314ec2a0a91f5ee435312f4a75588a16a864ac0a12e13d62696622c549ca',8864)
 im=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}
 assert actual=={r['path'] for r in im['files']}|set(im['excluded_exact_paths'])
 for r in im['files']:check(I/r['path'],r['sha256'],r['size'])
 for r in load(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(r[k]),r['sha256'],r['bytes'])
 for r in load(O/'flat-bindings.json'):check(pathlib.Path(r['path']),r['sha256'],r['size'])
 check(R/'manifest.json','4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)
 inv=load(R/'manifest.json');chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for r in chunks+inv['frozen_inputs']:check(R/r['path'],r['sha256'],r['bytes'])
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()==(R/'frozen'/n).read_bytes()
 cov=load(I/'coverage-delta.json');assert len(cov)==7783
 a=load(I/'active-breadth-reservations.json');res=load(I/'reserved-ids-r676.json');ids=set(res['ids'])
 assert len(ids)==50 and res['coverage_baseline']==7783
 assert ids=={r['mathdb_id'] for r in load(I/'queue-r676.json')}
 assert sum(x['lane']==O.name for x in a)==1
 assert next(x for x in a if x['lane']==O.name)['ids']==res['ids']
 for j,x in enumerate(a):
  s=set(x['ids']);assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
  for y in a[j+1:]:assert not s&set(y['ids'])
 w=load(O/'literal-records.json');d=load(O/'dispositions.json');assert len(w)==len(d)==50 and {x['mathdb_id'] for x in d}==ids
 assert {x['record']['mathdb_id'] for x in w}==ids
 byid={x['mathdb_id']:x for x in d};targets=collections.defaultdict(dict)
 for x in w:targets[x['chunk']][x['line']]=x['record']
 for p,items in targets.items():
  assert p in {str(R/r['path']) for r in chunks}
  found=set()
  with pathlib.Path(p).open() as f:
   for n,line in enumerate(f,1):
    if n in items:
     r=json.loads(line);assert r==items[n];found.add(n)
     z=byid[r['mathdb_id']];assert z['corpus_chunk']==p and z['corpus_line']==n
     assert z['statement']==r['statement'] and z['statement_utf8_sha256']==sha(r['statement'].encode())
     assert z['canonical_record_sha256']==sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
     assert z['independent_completeness'] in ['complete','incomplete','definition-dependent','scope-ambiguous'] and z['completeness_reason'] and z['technical_assessment']
     assert z['credit']==0 and not z['evidence_levels']['current_registry_cleared']
  assert found==set(items)
 assert len(load(O/'proposals.json'))<=3
 return {'integrity':'PASS','scientific_acceptance':False,'literal_reviews':50,'original_chunks':20,'frozen_inputs':8,'baseline':7783,'reservation_disjointness':True,'intake_exact_payload':True,'direct_original_copy_pairs':len(load(I/'bindings.json')),'manifest_sha256':sha((O/'manifest.json').read_bytes()),'manifest_size':(O/'manifest.json').stat().st_size}
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':payload(pathlib.Path(sys.argv[2]));print('PASS')
  else:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
