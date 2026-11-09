"""Independent read-only verifier. Execute only through the fixed helper_guard.py."""
import json,pathlib,hashlib,sys
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r587';C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert sha(b)==e['sha256'],f'hash mismatch: {p}'
def payload(root,manifest):
 excluded={'manifest.json','final-verification-receipt.json'} if root==O else {'manifest.json','verification-receipt.json'}
 names=[r['path'] for r in manifest['files']];assert len(names)==len(set(names)),'duplicate payload path'
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-set(excluded)==set(names),'extra/missing payload files'
 for r in manifest['files']:check(root/r['path'],r)
def verify():
 payload(O,load(O/'manifest.json'))
 for r in load(O/'initial-bindings.json')['files']:check(pathlib.Path(r['path']),r)
 for r in load(O/'flat-bindings.json'):check(pathlib.Path(r['path']),r)
 payload(I,load(I/'manifest.json'))
 pairs=load(I/'bindings.json')
 for r in pairs:
  check(pathlib.Path(r['original']),r);check(pathlib.Path(r['copy']),r)
 m=load(C/'manifest.json');chunks=[r for r in m['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(m['frozen_inputs'])==8
 for r in chunks+m['frozen_inputs']:check(C/r['path'],r)
 cov=set(map(int,load(I/'coverage-delta.json')));assert len(cov)==5633
 res=load(I/'reserved-ids.json');ids=set(res['ids']);assert len(ids)==50 and res['lane']==O.name and res['coverage_baseline']==5633
 assert ids=={r['mathdb_id'] for r in load(I/'queue.json')}
 sets=[]
 for r in load(I/'active-breadth-reservations.json'):
  s=set(r['ids']);assert len(s)==len(r['ids'])==50;assert not s&cov and not s&set(res['protected_ids']);assert all(not s&t for t in sets);sets.append(s)
 assert len(sets)==3 and ids in sets
 assert not ids&set(res['other_active_reservations'])
 rows=load(O/'literal-records.json');d=load(O/'dispositions.json');assert len(rows)==len(d)==50 and {x['mathdb_id'] for x in d}==ids
 originals={}
 for e in chunks:
  for n,line in enumerate((C/e['path']).open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in originals;originals[r['mathdb_id']]=(r,str(C/e['path']),n)
 assert set(originals)==ids
 assert len({x['record']['mathdb_id'] for x in rows})==50
 for x in rows:
  r,p,n=originals[x['record']['mathdb_id']];assert x['record']==r and x['corpus_chunk']==p and x['line']==n
  can=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());st=sha(r['statement'].encode());sz=len(r['statement'].encode())
  assert x['canonical_record_sha256']==can and x['statement_utf8_sha256']==st and x['statement_utf8_size']==sz
  a=next(y for y in d if y['mathdb_id']==r['mathdb_id']);assert a['literal_statement']==r['statement'] and a['canonical_record_sha256']==can and a['statement_utf8_sha256']==st and a['statement_utf8_size']==sz and a['corpus_chunk']==p and a['corpus_line']==n
  assert a['scope_flags']['literal_statement_read'] is True and a['scope_flags']['current_registry_cleared'] is False and a['accepted_credit']==0
 assert len(load(O/'proposals.json'))<=3
 for name in ['source-provenance.json','derivative-bindings.json']:
  for r in load(O/name):check(pathlib.Path(r['path']),r)
 return dict(integrity='PASS',mathematics='NOT_CERTIFIED',novelty='HOLD',records=50,baseline_record_reviews=5633,original_chunks=20,frozen_inputs=8,direct_pairs=len(pairs),active_disjoint_sets=3)
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
