"""Read-only independent verifier. Run with verify.sh (fixed helper guard)."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r629'
EXCLUDED={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(Path(p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(p,h,n):
 b=Path(p).read_bytes()
 assert len(b)==n,'size mismatch: '+str(p)
 assert sha(b)==h,'hash mismatch: '+str(p)
def payload(root,entries,excluded):
 expected={r['path'] for r in entries};assert len(expected)==len(entries),'duplicate manifest path'
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert not any(p.is_symlink() for p in root.rglob('*')),'symlink'
 assert actual-excluded==expected,'extra/missing payload files'
 for r in entries:blob(root/r['path'],r['sha256'],r['size'])
def verify():
 m=load(D/'manifest.json');assert set(m['excluded_exact_paths'])==EXCLUDED
 payload(D,m['files'],EXCLUDED)
 bindings=load(D/'flat-bindings.json');assert len({r['path'] for r in bindings})==len(bindings)
 for r in bindings:blob(r['path'],r['sha256'],r['size'])
 blob(I/'manifest.json','245456d3f80812f4ad23ee61c6353da454b3140d9e30649c2d3b0570c96edc9d',9327)
 im=load(I/'manifest.json');payload(I,im['files'],{'manifest.json','verification-receipt.json'})
 pairs=load(I/'bindings.json');assert len(pairs)==38
 for r in pairs:
  for k in ['original','copy']:blob(r[k],r['sha256'],r['bytes'])
 C=L/'pi-mathdb-full-corpus-inventory-r301';inv=load(C/'manifest.json')
 blob(C/'manifest.json','4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)
 chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20
 assert len(inv['frozen_inputs'])==8
 for r in chunks+inv['frozen_inputs']:blob(C/r['path'],r['sha256'],r['bytes'])
 # r304 live originals must equal the inventory's explicit immutable copies.
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  r=next(r for r in inv['frozen_inputs'] if r['path']=='frozen/'+name)
  blob(L/'root-mathdb-accepted-exclusions-r304'/name,r['sha256'],r['bytes'])
 cov=load(I/'coverage-delta.json');assert len(cov)==6633
 q=load(I/'queue-r630.json');a=load(I/'reserved-ids-r630.json');ids=a['ids'];assert len(ids)==len(set(ids))==50
 assert ids==[r['mathdb_id'] for r in q];assert a['coverage_baseline']==6633 and a['active_hypothesis_ids']==[]
 protected=set(a['protected_ids']);seen=set();active=load(I/'active-breadth-reservations.json');assert len(active)==3
 for r in active:
  s=set(r['ids']);assert len(s)==50 and not(s&seen) and not(s&set(map(int,cov))) and not(s&protected)
  assert r['active_hypothesis_ids']==[];seen|=s
 assert next(r['ids'] for r in active if r['lane']==D.name)==ids
 literal=load(D/'literal-records.json');dis=load(D/'dispositions.json');assert len(literal)==len(dis)==50
 assert set(ids)=={x['record']['mathdb_id'] for x in literal}=={x['mathdb_id'] for x in dis}
 dmap={x['mathdb_id']:x for x in dis};locations={}
 for x in literal:locations.setdefault(x['chunk'],{})[x['line']]=x
 for path,wanted in locations.items():
  assert path in {str(C/r['path']) for r in chunks}
  for n,b in enumerate(Path(path).open('rb'),1):
   if n not in wanted:continue
   x=wanted[n];r=json.loads(b);assert r==x['record'];d=dmap[r['mathdb_id']]
   h=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
   assert h==x['canonical_record_sha256']==d['canonical_record_sha256']
   assert d['statement_utf8']==r['statement'] and d['statement_utf8_sha256']==sha(r['statement'].encode())
   assert d['corpus_chunk']==path and d['corpus_line']==n
   assert d['accepted_credit']==0 and not d['current_registry_cleared'] and not d['full_dependency_audit']
 assert load(D/'proposals.json')==[]
 for file in ['source-provenance.json','pdf-provenance.json']:
  for r in load(D/file):
   if 'path' in r:blob(D/r['path'],r['sha256'],r['size'])
   if 'derivative' in r:
    t=r['derivative'];blob(D/t['path'],t['sha256'],t['size'])
 for r in load(D/'derivative-bindings.json'):blob(D/r['path'],r['sha256'],r['size'])
 return {'integrity':'PASS','scientific_acceptance':False,'original_chunks':20,'frozen_inputs':8,'original_copy_pairs':38,'literal_records':50,'proposals':0,'coverage_baseline':6633,'reservation_disjointness':True,'payload_files':len(m['files']),'manifest_sha256':sha((D/'manifest.json').read_bytes()),'manifest_size':(D/'manifest.json').stat().st_size}
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
