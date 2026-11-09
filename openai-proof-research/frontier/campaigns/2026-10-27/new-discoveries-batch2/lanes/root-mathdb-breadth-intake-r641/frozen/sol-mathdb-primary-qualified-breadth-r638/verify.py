"""Read-only independent verifier. Run via verify.sh. Optional --negative=hash|size|extra injects bounded in-memory corruption into own payload checking only."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r637';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def ck(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert h(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m,negative=None):
 names={e['path'] for e in m['files']};assert len(names)==len(m['files']);actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()};assert not any(p.is_symlink() for p in root.rglob('*'))
 if negative=='extra':actual.add('injected-extra-file')
 assert actual-set(m['excluded_exact_paths'])==names,'extra/missing file'
 for e in m['files']:
  b=(root/e['path']).read_bytes()
  if e==m['files'][0] and negative=='hash':b=bytes([b[0]^1])+b[1:]
  if e==m['files'][0] and negative=='size':b+=b'!'
  assert len(b)==e.get('size',e.get('bytes')),'size mismatch'
  assert h(b)==e['sha256'],'hash mismatch'
def main():
 initial=j(P/'initial-bindings.json')
 for e in initial:ck(pathlib.Path(e['path']),e)
 for e in j(P/'flat-bindings.json'):ck(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  for k in ['original','copy']:ck(pathlib.Path(e[k]),e)
 inv=j(C/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:ck(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==6833
 active=j(I/'active-breadth-reservations.json');assert len(active)==3;seen=set()
 for r in active:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);assert r['active_hypothesis_ids']==[];seen|=ids
 for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
 res=j(I/'reserved-ids-r638.json');ids=set(res['ids']);assert len(ids)==50 and ids=={r['mathdb_id'] for r in j(I/'queue-r638.json')};assert res['coverage_baseline']==6833
 assert next(r for r in active if r['lane']==P.name)['ids']==res['ids']
 assert next(r for r in active if 'r628' in r['lane'])['status']=='rate_limit_held_not_reconciled'
 assert sum(1 for _ in (I/'routing-queue.jsonl').open())==8000
 ds=j(P/'dispositions.json');literal=j(P/'literal-records.json');assert len(ds)==len(literal)==50 and {d['mathdb_id'] for d in ds}==ids and {d['mathdb_id'] for d in literal}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 assert len(found)==50
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert d['corpus_chunk']==str(p) and d['corpus_line']==n;assert d['statement_utf8']==r['statement'];assert d['statement_utf8_sha256']==h(r['statement'].encode());assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['source_url']==r['source_url'];assert d['accepted_credit']==0 and not d['current_registry_cleared'] and not d['full_scope_proof_established'];assert sum(d['flags'].values())==1
 for d in literal:
  p,n,r=found[d['mathdb_id']];assert d['record']==r and d['corpus_chunk']==str(p) and d['corpus_line']==n;assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert d['statement_utf8_sha256']==h(r['statement'].encode())
 assert j(P/'proposals.json')==[]
 for f in ['fetch-provenance.json','pdf-bindings.json','derivative-bindings.json']:
  for e in j(P/f):assert 'error' not in e;ck(P/e['path'],e)
 for f in ['prior-bindings.json','prior-derivative.json']:
  e=j(P/f);assert 'error' not in e;ck(P/e['path'],e)
 for e in j(P/'selected-passages.json'):assert e['text']=='\n'.join((P/e['file']).read_text().splitlines()[e['start_line']-1:e['end_line']])
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];neg=next((s.split('=',1)[1] for s in sys.argv if s.startswith('--negative=')),None);assert neg in [None,'hash','size','extra'];exact(P,m,neg)
 return dict(integrity='PASS',literal_records=50,primary_passage_records=15,whole_primary_bodies=0,local_proof_bodies=1,full_dependency_audits=0,proposals=0,credit=0,intake_exact=True,direct_original_copy_pairs=len(j(I/'bindings.json')),original_chunks=20,frozen_inputs=8,reservations_disjoint=True,baseline=6833,math_novelty_acceptance=False)
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print(json.dumps(dict(integrity='FAIL',error=str(e))),file=sys.stderr);sys.exit(1)
