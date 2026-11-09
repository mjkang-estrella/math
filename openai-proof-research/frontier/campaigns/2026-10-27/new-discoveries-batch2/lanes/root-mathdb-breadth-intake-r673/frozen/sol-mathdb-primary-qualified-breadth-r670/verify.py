#!/usr/bin/env python3
"""Independent read-only verifier. Run under the fixed helper guard."""
from pathlib import Path
import argparse,hashlib,json,sys
O=Path(__file__).resolve().parent
L=O.parent; I=L/'root-mathdb-breadth-intake-r669'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def read(p): return json.loads(p.read_text())
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b);n+=len(b)
 return h.hexdigest(),n
def check(p,e):
 h,n=digest(p)
 assert h==e['sha256'], 'hash mismatch: '+str(p)
 assert n==e.get('size',e.get('bytes')), 'size mismatch: '+str(p)
def payload(base,m):
 names=[e['path'] for e in m['files']]
 assert len(names)==len(set(names)), 'duplicate manifest path'
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
 actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
 assert actual==set(names)|set(m['excluded_exact_paths']), 'extra/missing payload file'
 for e in m['files']: check(base/e['path'],e)
def run(expected=None,size=None):
 m=read(O/'manifest.json')
 assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 if expected: assert digest(O/'manifest.json')==(expected,size), 'manifest anchor mismatch'
 payload(O,m)
 for e in read(O/'flat-bindings.json'):check(Path(e['path']),e)
 for e in read(O/'initial-bindings.json'):check(Path(e['path']),e)
 im=read(I/'manifest.json');payload(I,im)
 pairs=read(I/'bindings.json')
 for e in pairs:
  check(Path(e['original']),e);check(Path(e['copy']),e)
 rm=read(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 active=read(I/'active-breadth-reservations.json');coverage=set(map(int,read(I/'coverage-delta.json')))
 assert len(coverage)==7633
 sets=[]
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&coverage and not s&set(a['protected_ids'])
  assert all(not s&t for t in sets);sets.append(s)
 reserve=read(I/'reserved-ids-r670.json');ids=reserve['ids']
 assert reserve['lane']==O.name and reserve['coverage_baseline']==7633
 assert ids==[q['mathdb_id'] for q in read(I/'queue-r670.json')]
 assert set(ids)==set(next(a['ids'] for a in active if a['lane']==O.name))
 literals=read(O/'literal-records.json');disp=read(O/'dispositions.json')
 assert len(literals)==len(disp)==50 and [x['mathdb_id'] for x in disp]==ids
 assert {x['record']['mathdb_id'] for x in literals}==set(ids)
 byid={x['mathdb_id']:x for x in disp}
 grouped={}
 for x in literals:grouped.setdefault(x['chunk'],{})[x['line']]=x
 count=0
 for chunk,needed in grouped.items():
  for n,line in enumerate((R/chunk).open(encoding='utf-8'),1):
   if n not in needed:continue
   x=needed[n];record=json.loads(line);assert record==x['record']
   canon=json.dumps(record,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')
   h=hashlib.sha256(canon).hexdigest();assert h==x['canonical_record_sha256']
   d=byid[record['mathdb_id']]
   assert d['canonical_record_sha256']==h and d['statement']==record['statement']
   assert d['statement_utf8_sha256']==hashlib.sha256(record['statement'].encode('utf-8')).hexdigest()
   assert d['corpus_chunk']==chunk and d['corpus_line']==n
   assert d['statement_completeness'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
   assert d['completeness_reason'] and d['technical_assessment'] and d['accepted_credit']==0
   count+=1
 assert count==50
 assert read(O/'proposals.json')==[]
 for e in read(O/'source-provenance.json'):
  if 'path' in e:check(O/e['path'],e)
 for name in ['derivative-bindings.json','image-bindings.json']:
  for e in read(O/name):check(O/e['path'],e)
 lb=read(O/'literal-binding.json');check(Path(lb['path']),lb)
 return dict(integrity='PASS',literal_reviews=50,baseline=7633,corpus_chunks=20,frozen_inputs=8,direct_pairs=len(pairs),proposals=0,mathematics='NOT A PASS; screening only',novelty='HOLD',manifest_sha256=digest(O/'manifest.json')[0],manifest_size=digest(O/'manifest.json')[1])
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--manifest-sha256');p.add_argument('--manifest-size',type=int);p.add_argument('--fixture-base');p.add_argument('--fixture-manifest');a=p.parse_args()
 try:
  if a.fixture_base:
   payload(Path(a.fixture_base),read(Path(a.fixture_manifest)));print('fixture PASS')
  else: print(json.dumps(run(a.manifest_sha256,a.manifest_size),sort_keys=True))
 except Exception as e: print('FAIL: '+repr(e),file=sys.stderr);sys.exit(1)
