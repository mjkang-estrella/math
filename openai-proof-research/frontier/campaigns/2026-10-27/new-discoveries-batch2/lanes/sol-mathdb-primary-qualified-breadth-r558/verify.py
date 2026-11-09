#!/usr/bin/env python3
"""Read-only independent integrity verifier. Run under the fixed helper guard."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_bytes())
def digest(p):
 b=p.read_bytes();return len(b),hashlib.sha256(b).hexdigest()
def check(p,e):
 assert p.is_file() and not p.is_symlink(),f'missing/symlink {p}'
 s,h=digest(p);assert s==e.get('size',e.get('bytes')),f'size mismatch {p}'
 assert h==e['sha256'],f'hash mismatch {p}'
def payload(root):
 m=load(root/'manifest.json');assert set(m['excluded_exact_paths'])==EX
 paths={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 assert paths-EX==expected,f'extra/missing payload {paths-EX ^ expected}'
 for e in m['files']:check(root/e['path'],e)
def verify():
 payload(D);L=D.parent;I=L/'root-mathdb-breadth-intake-r557';R=L/'pi-mathdb-full-corpus-inventory-r301'
 refs=load(D/'flat-bindings.json')
 for e in refs:check(Path(e['path']),e)
 bound={e['path']:e for e in refs};assert str(I/'manifest.json') in bound and str(I/'verify.py') in bound
 im=load(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im['files']}|{'manifest.json','verification-receipt.json'}
 for e in im['files']:check(I/e['path'],e)
 for e in load(I/'bindings.json'):
  for k in ['original','copy']:check(Path(e[k]),e)
 assert str(R/'manifest.json') in bound
 rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  assert digest(L/'root-mathdb-accepted-exclusions-r304'/name)==digest(R/'frozen'/name)
 cov=load(I/'coverage-delta.json');assert len(cov)==4883
 res=load(I/'reserved-ids.json');assigned=set(res['ids']);assert len(assigned)==50
 q=load(I/'queue.json');assert len(q)==50 and {e['mathdb_id'] for e in q}==assigned
 assert res['lane']==D.name and res['coverage_baseline']==4883 and not res['active_hypothesis_ids']
 seen=set();other=set()
 for r in load(I/'active-breadth-reservations.json'):
  s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(res['protected_ids']);seen|=s
  if r['lane']!=D.name:other|=s
 assert other==set(res['other_active_reservations']) and not assigned&other
 rows=load(D/'dispositions.json');assert len(rows)==50 and {e['mathdb_id'] for e in rows}==assigned
 index={e['mathdb_id']:e for e in rows};found={}
 for ce in chunks:
  p=R/ce['path']
  for n,line in enumerate(p.open(encoding='utf8'),1):
   x=json.loads(line);i=x['mathdb_id']
   if i in assigned:
    assert i not in found;found[i]=x;d=index[i]
    assert d['corpus_chunk']==str(p) and d['corpus_line']==n and d['statement']==x['statement']
    assert d['statement_utf8_sha256']==hashlib.sha256(x['statement'].encode()).hexdigest()
    assert d['canonical_record_sha256']==hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    assert d['literal_statement_read'] and not d['current_registry_cleared'] and d['accepted_credit']==0
 assert set(found)==assigned
 ar=load(D/'assigned-records.json');assert len(ar)==50
 for r in ar:assert r['record']==found[r['record']['mathdb_id']]
 assert load(D/'proposals.json')==[]
 for e in load(D/'source-provenance.json'):
  check(D/(e['name']+'.pdf'),e);check(D/e['derivative']['path'],e['derivative'])
 return {'integrity':'PASS','literal_reviews':50,'baseline':4883,'proposals':0,'chunks_in_place':20,'frozen_inputs':8,'registry':'HOLD','math_novelty':'NOT_CERTIFIED'}
if __name__=='__main__':
 try:
  if len(sys.argv)==3 and sys.argv[1]=='--payload-only':payload(Path(sys.argv[2]));print('PASS payload fixture')
  else:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print('FAIL '+repr(e),file=sys.stderr);sys.exit(1)
