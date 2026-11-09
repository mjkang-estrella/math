#!/usr/bin/env python3
"""Independent, read-only verifier. Run through the fixed resource guard."""
import argparse,hashlib,json,sys
from pathlib import Path

def load(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}'
 assert hashlib.sha256(b).hexdigest()==e['sha256'],f'hash mismatch: {p}'
def payload(root):
 m=load(root/'manifest.json');ex=['manifest.json','final-verification-receipt.json'];assert m['excluded_exact_paths']==ex
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert actual-set(ex)==expected,'extra or missing payload file'
 for e in m['files']:check(root/e['path'],e)
def verify(root):
 payload(root)
 flat=load(root/'flat-bindings.json')
 for e in flat:check(Path(e['path']),e)
 for e in load(root/'initial-bindings.json'):check(Path(e['path']),e)
 initial=load(root/'initial-bindings.json');I=Path(next(e['path'] for e in initial if e['path'].endswith('/queue.json'))).parent;L=I.parent;R=L/'pi-mathdb-full-corpus-inventory-r301'
 m=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
 for e in m['files']:check(I/e['path'],e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(Path(e['original']),e);check(Path(e['copy']),e)
 inv_binding=next(e for e in pairs if e['original']==str(R/'manifest.json'));check(R/'manifest.json',inv_binding)
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 res=load(I/'reserved-ids.json');q=load(I/'queue.json');cov=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json');assert len(cov)==4133
 protected=set(res['protected_ids']);sets=[set(r['ids']) for r in active]
 assert len(sets)==3
 for i,(s,r) in enumerate(zip(sets,active)):
  assert len(s)==len(r['ids'])==50 and not s&set(map(int,cov)) and not s&protected
  assert set(r['protected_ids'])==protected
  assert set(r['other_active_reservations'])==set.union(*(t for j,t in enumerate(sets) if j!=i))
  for t in sets[:i]:assert not s&t
 ids=set(res['ids']);assert len(ids)==50 and ids=={r['mathdb_id'] for r in q}
 assert next(r for r in active if r['lane']==res['lane'])==res
 assigned=load(root/'assigned-records.json');d=load(root/'dispositions.json');assert len(assigned)==len(d)==50
 assert {e['record']['mathdb_id'] for e in assigned}==ids and {e['mathdb_id'] for e in d}==ids
 byid={e['mathdb_id']:e for e in d}
 # Read only actual original corpus lines, never local copies.
 positions={str((R/e['path']).resolve()):{} for e in chunks}
 for e in assigned:positions[e['chunk']][e['line']]=e
 found=0
 for path,loc in positions.items():
  with Path(path).open('rb') as f:
   for line,b in enumerate(f,1):
    if line not in loc:continue
    e=loc[line];r=json.loads(b);assert r==e['record'];i=r['mathdb_id'];z=byid[i]
    sh=hashlib.sha256(r['statement'].encode('utf-8')).hexdigest();ch=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')).hexdigest()
    assert sh==e['statement_sha256']==z['statement_sha256'] and ch==e['canonical_record_sha256']==z['canonical_record_sha256']
    assert z['literal_statement']==r['statement'] and z['corpus_chunk']==path and z['corpus_line']==line
    assert z['credit']==0 and z['novelty_pass'] is False;found+=1
 assert found==50
 assert len(load(root/'proposals.json'))<=3
 for n in ['source-bindings.json','derivative-bindings.json']:
  for e in load(root/n):
   if 'path' in e:check(Path(e['path']),e)
 print(json.dumps(dict(integrity='PASS',literal_records=found,corpus_chunks=20,frozen_inputs=8,baseline=4133,direct_pairs=len(pairs),math_or_novelty_pass=False)))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--payload-root',type=Path,default=Path(__file__).resolve().parent);args=ap.parse_args()
 try:verify(args.payload_root.resolve())
 except Exception as ex:print('FAIL: '+str(ex),file=sys.stderr);sys.exit(1)
