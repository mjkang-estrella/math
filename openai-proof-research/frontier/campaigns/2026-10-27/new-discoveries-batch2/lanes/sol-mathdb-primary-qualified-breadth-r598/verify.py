"""Independent read-only verifier. Never executes upstream code. Nonzero on mismatch."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r597'
def load(p):return json.loads(p.read_text())
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return n,h.hexdigest()
def check(p,r):
 n,h=digest(p);assert n==r.get('size',r.get('bytes')),f'size mismatch {p}';assert h==r['sha256'],f'hash mismatch {p}'
def payload(root):
 m=load(root/'manifest.json');excluded={'manifest.json','final-verification-receipt.json'};assert set(m['excluded_exact_paths'])==excluded
 names=[r['path'] for r in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-excluded==set(names),'extra/missing payload file'
 for r in m['files']:
  p=root/r['path'];assert p.is_relative_to(root) and '..' not in pathlib.Path(r['path']).parts;check(p,r)
def main():
 if len(sys.argv)>1:
  assert sys.argv[1]=='--payload-only';payload(pathlib.Path(sys.argv[2]).resolve());return {'payload':'PASS'}
 payload(P)
 flat=load(P/'flat-bindings.json');assert len(flat)==len({r['path'] for r in flat})
 for r in flat:check(pathlib.Path(r['path']),r)
 check(I/'manifest.json',{'size':9547,'sha256':'99dbb14e5f76cdd68dc3393a39727e184e68079f69b471575ababab182582909'})
 im=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={r['path'] for r in im['files']}|set(im['excluded_exact_paths'])
 for r in im['files']:check(I/r['path'],r)
 pairs=load(I/'bindings.json')
 for r in pairs:
  for k in ['original','copy']:check(pathlib.Path(r[k]),r)
  assert pathlib.Path(r['original']).read_bytes()==pathlib.Path(r['copy']).read_bytes()
 R=L/'pi-mathdb-full-corpus-inventory-r301';rm=load(R/'manifest.json');inv=[r for r in pairs if r['original']==str(R/'manifest.json')];assert len(inv)==1;check(R/'manifest.json',inv[0])
 chunks=[r for r in rm['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20;assert len(rm['frozen_inputs'])==8
 for r in chunks+rm['frozen_inputs']:check(R/r['path'],r)
 reserve=load(I/'reserved-ids.json');ids=set(reserve['ids']);assert len(ids)==50 and reserve['lane']==P.name;assert reserve['coverage_baseline']==5883
 queue=load(I/'queue.json');assert {r['mathdb_id'] for r in queue}==ids and len(queue)==50
 coverage=load(I/'coverage-delta.json');assert len(coverage)==5883;covered={int(i) for i in coverage}
 protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439};assert set(reserve['protected_ids'])==protected
 active=load(I/'active-breadth-reservations.json');assert len(active)==3;sets=[]
 for a in active:
  s=set(a['ids']);assert len(s)==len(a['ids'])==50;assert not s&covered and not s&protected
  for t in sets:assert not s&t
  sets.append(s)
 assert ids in sets
 assert set(reserve['other_active_reservations'])==set.union(*(s for s in sets if s!=ids))
 literals=load(P/'literal-records.json');disp=load(P/'dispositions.json');assert len(literals)==len(disp)==50;assert {r['mathdb_id'] for r in literals}=={r['mathdb_id'] for r in disp}==ids
 lit={r['mathdb_id']:r for r in literals};seen=set()
 for c in chunks:
  for n,line in enumerate((R/c['path']).open(),1):
   d=json.loads(line);i=d['mathdb_id']
   if i not in ids:continue
   r=lit[i];assert i not in seen;seen.add(i);assert r['chunk']==str(R/c['path']) and r['line']==n and r['record']==d
   assert r['statement']==d['statement'];assert r['statement_sha256']==hashlib.sha256(d['statement'].encode('utf-8')).hexdigest()
   assert r['canonical_record_sha256']==hashlib.sha256(json.dumps(d,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')).hexdigest()
 assert seen==ids
 for d in disp:
  r=lit[d['mathdb_id']]
  for k in ['chunk','line','statement','statement_sha256','canonical_record_sha256']:assert d[k]==r[k]
  assert d['scope_flags']['literal_record_statement_read'] and not d['scope_flags']['current_registry_cleared'] and d['credit']==0
 assert len(load(P/'proposals.json'))==0
 for r in load(P/'source-provenance.json')+load(P/'derivative-bindings.json'):check(pathlib.Path(r['path']),r)
 return {'integrity':'PASS','intake_payload':'exact','original_copy_pairs':len(pairs),'original_chunks':20,'frozen_inputs':8,'baseline_record_reviews':5883,'assigned_literal_records':50,'active_disjoint_sets':3,'proposals':0,'math_novelty':'NOT_CERTIFIED'}
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
