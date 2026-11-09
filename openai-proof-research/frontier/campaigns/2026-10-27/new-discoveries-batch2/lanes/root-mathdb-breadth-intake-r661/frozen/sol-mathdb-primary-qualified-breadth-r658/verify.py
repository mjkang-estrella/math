"""Independent read-only verification. Invoke via verify.sh; no upstream verifier executed."""
import pathlib,json,hashlib,sys,collections
O=pathlib.Path(__file__).resolve().parent
class Mismatch(Exception):pass
def require(v,m):
 if not v:raise Mismatch(m)
def digest(d):return hashlib.sha256(d).hexdigest()
def load(p):return json.loads(p.read_text())
def bound(p,r):
 d=p.read_bytes();require(len(d)==r.get('size',r.get('bytes')),f'size mismatch: {p}');require(digest(d)==r['sha256'],f'hash mismatch: {p}')
def payload(root,m):
 files=m['files'];expected={r['path'] for r in files};require(len(expected)==len(files),'duplicate manifest path')
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};require(actual==expected|{n for n in m['excluded_exact_paths'] if (root/n).exists()},'exact payload mismatch')
 for r in files:
  p=root/r['path'];require(not p.is_symlink() and '..' not in pathlib.Path(r['path']).parts,'unsafe file');bound(p,r)
def main():
 m=load(O/'manifest.json');require(m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'],'exclusions');payload(O,m)
 receipt=O/'final-verification-receipt.json'
 if receipt.exists():bound(O/'manifest.json',load(receipt)['manifest'])
 refs=load(O/'flat-bindings.json');initial=load(O/'initial-bindings.json')
 for r in refs+initial:bound(pathlib.Path(r['path']),r)
 L=O.parent;I=L/'root-mathdb-breadth-intake-r657';payload(I,load(I/'manifest.json'))
 for r in load(I/'bindings.json'):
  for k in ['original','copy']:bound(pathlib.Path(r[k]),r)
 base=L/'pi-mathdb-full-corpus-inventory-r301';inv=load(base/'manifest.json');chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')];require(len(chunks)==20 and len(inv['frozen_inputs'])==8,'inventory cardinality')
 for r in chunks+inv['frozen_inputs']:bound(base/r['path'],r)
 res=load(I/'reserved-ids-r658.json');ids=res['ids'];require(len(ids)==50 and len(set(ids))==50,'reserved cardinality');queue=load(I/'queue-r658.json');require([r['mathdb_id'] for r in queue]==ids,'queue exact ids/order')
 cov=load(I/'coverage-delta.json');require(len(cov)==7333,'coverage baseline');active=load(I/'active-breadth-reservations.json');require(len(active)==3,'three active lanes')
 require(set(ids)==set(next(a['ids'] for a in active if a['lane']==O.name)),'active assignment mismatch')
 for j,a in enumerate(active):
  require(len(a['ids'])==len(set(a['ids'])),'duplicate reserved id');require(not set(a['ids'])&set(map(int,cov)),'coverage overlap');require(not set(a['ids'])&set(a['protected_ids']),'protected overlap')
  for b in active[j+1:]:require(not set(a['ids'])&set(b['ids']),'reservation overlap')
 bound(O/'literal-records.json',load(O/'literal-binding.json'));lits=load(O/'literal-records.json');disp=load(O/'dispositions.json');require(len(lits)==len(disp)==50,'literal/disposition cardinality');require([r['mathdb_id'] for r in disp]==ids,'disposition ids/order')
 originals={}
 for r in chunks:
  p=base/r['path']
  for n,line in enumerate(p.open(),1):
   obj=json.loads(line)
   if obj['mathdb_id'] in set(ids):originals[obj['mathdb_id']]=(str(p.resolve()),n,obj)
 for x,d in zip(lits,disp):
  v=x['record'];k=v['mathdb_id'];p,n,obj=originals[k];require(v==obj,'literal record mismatch');require(x['corpus_path']==p and x['line']==n,'literal locator mismatch');h=digest(json.dumps(obj,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());require(x['canonical_record_sha256']==d['canonical_record_sha256']==h,'canonical hash');require(d['statement']==obj['statement'] and d['statement_utf8_sha256']==digest(obj['statement'].encode()),'statement mismatch');require(d['corpus_path']==p and d['corpus_line']==n,'disposition locator');require(d['completeness']['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and bool(d['completeness']['reason']),'classification/reason');require(d['accepted_credit']==0,'credit')
 require(len(load(O/'proposals.json'))<=3,'proposal cap')
 return {'integrity':'PASS','literal_records':50,'corpus_chunks_verified_in_place':20,'frozen_inputs_verified':8,'intake_pairs_verified':len(load(I/'bindings.json')),'reserved_sets':3,'baseline':7333,'classification_counts':dict(collections.Counter(r['completeness']['classification'] for r in disp)),'math_and_novelty':'NOT PASS: no proposed theorem; registry HOLD; disclosed derivative-binding timing deviation'}
if __name__=='__main__':
 try: print(json.dumps(main(),sort_keys=True))
 except Exception as e:print(f'FAIL: {type(e).__name__}: {e}',file=sys.stderr);sys.exit(1)
