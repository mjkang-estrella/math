"""Read-only independent verifier. Run through fixed helper_guard.py. Nonzero on mismatch."""
from pathlib import Path
import hashlib,json,sys,itertools
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r541';R=L/'pi-mathdb-full-corpus-inventory-r301'
def H(b):return hashlib.sha256(b).hexdigest()
def J(p):return json.loads(p.read_bytes())
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert H(b)==e['sha256'],('hash',str(p))
def payload_check(actual,m):
 expected={e['path']:e for e in m['files']}
 assert set(actual)==set(expected),('payload names',set(actual)^set(expected))
 for name,b in actual.items():assert len(b)==expected[name]['size'],('size',name);assert H(b)==expected[name]['sha256'],('hash',name)
def main():
 m=J(O/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 actual={str(p.relative_to(O)):p.read_bytes() for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in m['excluded_exact_paths']}
 neg=sys.argv[1:]
 if neg:
  assert len(neg)==1 and neg[0] in ['--negative-hash','--negative-size','--negative-extra']
  if neg[0]=='--negative-extra':actual['NEGATIVE.extra']=b'x'
  else:
   name='SUMMARY.md';b=actual[name];actual[name]=(bytes([b[0]^1])+b[1:]) if neg[0]=='--negative-hash' else b+b'x'
 payload_check(actual,m)
 if (O/'final-verification-receipt.json').exists():
  rec=J(O/'final-verification-receipt.json');check(O/'manifest.json',rec['manifest'])
 for e in J(O/'flat-bindings.json'):check(Path(e['path']),e)
 assert H((I/'manifest.json').read_bytes())=='cb5a7055f1988395c09ac7deedcbedd7830ec5af2fb21b242ed8cfc45579f7a0'
 im=J(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 pairs=J(I/'bindings.json')
 for e in pairs:
  check(Path(e['original']),e);check(Path(e['copy']),e)
 pinned=next(e for e in im['files'] if e['path']=='frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json');check(R/'manifest.json',pinned)
 rm=J(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20;assert len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 # Direct r304 originals versus the inventory's frozen r304 copies.
 for name in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (L/'root-mathdb-accepted-exclusions-r304'/name).read_bytes()==(R/'frozen/root-mathdb-accepted-exclusions-r304'/name).read_bytes()
 s=J(I/'reserved-ids.json');ids=set(s['ids']);assert len(ids)==50;assert s['lane']==O.name
 cov=set(map(int,J(I/'coverage-delta.json')));assert len(cov)==4483
 groups=J(I/'active-breadth-reservations.json');assert len(groups)==3;union=set()
 for g in groups:
  gs=set(g['ids']);assert len(gs)==50 and not gs&union and not gs&cov and not gs&set(s['protected_ids']);union|=gs
 assert union-ids==set(s['other_active_reservations']);assert ids==set(next(g['ids'] for g in groups if g['lane']==O.name))
 assert ids=={e['mathdb_id'] for e in J(I/'queue.json')}
 assert not s['active_hypothesis_ids'];assert 366370 in s['protected_ids']
 D=J(O/'dispositions.json');A=J(O/'assigned-records.json');assert len(D)==len(A)==50
 assert {a['record']['mathdb_id'] for a in A}==ids=={d['mathdb_id'] for d in D}
 assert J(O/'proposals.json')==[]
 originals={}
 for e in chunks:
  with (R/e['path']).open() as f:
   for n,line in enumerate(f,1):
    x=json.loads(line)
    if x['mathdb_id'] in ids:
     assert x['mathdb_id'] not in originals
     originals[x['mathdb_id']]=(str(R/e['path']),n,x)
 assert len(originals)==50
 for a,d in zip(A,D):
  r=a['record'];key=r['mathdb_id'];chunk,n,x=originals[key]
  assert r==x and a['chunk']==chunk and a['line']==n
  assert d['mathdb_id']==key and d['corpus_chunk']==chunk and d['corpus_line']==n
  assert d['statement_utf8']==x['statement'] and d['statement_sha256']==H(x['statement'].encode())
  assert d['canonical_record_sha256']==H(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['literal_full_statement_read'] and d['credit']==0 and d['technical_screen']
 for name in ['retrieval-bindings.json','retrieval2-bindings.json','retrieval3-bindings.json','derivative-bindings.json','derivative2-bindings.json','derivative3-bindings.json']:
  for e in J(O/name):
   if 'path' in e:check(Path(e['path']),e)
 c=J(O/'bounded-calculation.json');F=list(itertools.product(range(2),repeat=6));F=[list(x) for x in F if sum(x)<=2]
 assert c['family']==F and len(F)==22 and c['conjectured_terms']==[17,20]
 assert c['minimum_pair_agreement']==min(sum(x==y for x,y in zip(a,b)) for a,b in itertools.combinations(F,2))==2
 assert c['fixed_coordinates']==[j for j in range(6) if len({x[j] for x in F})==1]==[]
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'proposals':0,'baseline':4483,'original_chunks':20,'frozen_inputs':8,'direct_pairs':len(pairs),'math_novelty':'NOT_CERTIFIED'}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL: '+repr(e),file=sys.stderr);sys.exit(1)
