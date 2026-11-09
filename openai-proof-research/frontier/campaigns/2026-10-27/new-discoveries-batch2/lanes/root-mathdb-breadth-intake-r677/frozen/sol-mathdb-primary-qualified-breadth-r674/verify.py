#!/usr/bin/env python3
"""Independent read-only verifier. Run through verify.sh / fixed helper guard.
--negative-test tests an in-memory bad payload view; never changes disk inputs.
"""
import json,hashlib,sys
from pathlib import Path
O=Path(__file__).resolve().parent
L=O.parent
I=L/'root-mathdb-breadth-intake-r673'
R=L/'pi-mathdb-full-corpus-inventory-r301'
EXCLUDED={'manifest.json','final-verification-receipt.json'}
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_bytes())
def check(p,e):
 b=p.read_bytes()
 assert len(b)==e.get('size',e.get('bytes')), 'size mismatch: '+str(p)
 assert sha(b)==e['sha256'], 'hash mismatch: '+str(p)
def canonical(r):return sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
def main():
 m=j(O/'manifest.json')
 assert set(m['excluded_exact_paths'])==EXCLUDED
 entries=m['files'];names=[e['path'] for e in entries]
 assert len(names)==len(set(names))
 actual={str(p.relative_to(O)):p.read_bytes() for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in EXCLUDED}
 assert not any(p.is_symlink() for p in O.rglob('*')), 'symlink'
 if len(sys.argv)>1:
  assert sys.argv[1]=='--negative-test' and len(sys.argv)==3
  kind=sys.argv[2];n='proposals.json'
  if kind=='hash': actual[n]=b'X'+actual[n][1:]
  elif kind=='size':actual[n]+=b' '
  elif kind=='extra':actual['UNLISTED']=b'negative'
  else:raise ValueError(kind)
 assert set(actual)==set(names), 'extra/missing payload'
 for e in entries:
  b=actual[e['path']];assert len(b)==e['size'], 'payload size';assert sha(b)==e['sha256'], 'payload hash'
 # Bind intake manifest and exact payload independently; upstream verify.py is never run.
 assert sha((I/'manifest.json').read_bytes())=='8a4ac176b6d78928e2b82294cf8b1331fe04956616190ac9e64e7f88a5d7d7e8'
 im=j(I/'manifest.json');expected={e['path'] for e in im['files']}
 got={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])
 assert got==expected, 'intake payload set'
 for e in im['files']:check(I/e['path'],e)
 for e in j(I/'bindings.json'):
  check(Path(e['original']),e);check(Path(e['copy']),e)
 for e in j(O/'flat-bindings.json'):check(Path(e['path']),e)
 assert sha((R/'manifest.json').read_bytes())=='4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15'
 inv=j(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 res=j(I/'reserved-ids-r674.json');ids=set(res['ids']);q=j(I/'queue-r674.json')
 assert len(ids)==len(q)==50 and ids=={x['mathdb_id'] for x in q}
 cov=j(I/'coverage-delta.json');assert len(cov)==7733
 sets=[set(x['ids']) for x in j(I/'active-breadth-reservations.json')]
 assert len(sets)==3 and ids in sets
 for k,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,cov)) and not s&set(res['protected_ids'])
  for t in sets[:k]:assert not s&t
 lit=j(O/'literal-records.json');disp=j(O/'dispositions.json')
 assert len(lit)==len(disp)==50
 assert {x['record']['mathdb_id'] for x in lit}==ids=={x['mathdb_id'] for x in disp}
 assert len({x['mathdb_id'] for x in disp})==50
 by={x['mathdb_id']:x for x in disp}
 for x in lit:
  p=Path(x['chunk']);assert str(p) in {str(R/e['path']) for e in chunks}
  with p.open() as f:
   for n,line in enumerate(f,1):
    if n==x['line']:actual_record=json.loads(line);break
   else:raise AssertionError('line missing')
  assert actual_record==x['record']
  r=x['record'];d=by[r['mathdb_id']]
  assert canonical(r)==x['canonical_record_sha256']==d['canonical_record_sha256']
  assert r['statement']==d['exact_utf8_statement']
  assert sha(r['statement'].encode())==d['statement_sha256']
  assert d['corpus_chunk']==x['chunk'] and d['corpus_line']==x['line']
  assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'}
  assert d['classification_reason'] and d['technical_assessment'] and d['accepted_credit']==0
 assert len(j(O/'proposals.json'))==0
 for name in ['source-provenance.json','derivative-bindings.json','image-bindings.json']:
  for e in j(O/name):check(Path(e['path']),e)
 check(O/'literal-records.json',j(O/'literal-binding.json'))
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'original_chunks':20,'frozen_inputs':8,'baseline':7733,'reservation_disjointness':True,'proposals':0,'scientific_acceptance':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
