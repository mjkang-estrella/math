#!/usr/bin/env python3
"""Independent read-only integrity verifier. Run through verify.sh (fixed guard)."""
from pathlib import Path
import json,hashlib,sys,copy
O=Path(__file__).resolve().parent
I=O.parent/'root-mathdb-breadth-intake-r679'
R=O.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(Path(p).read_text())
def digest(p):
 b=Path(p).read_bytes();return hashlib.sha256(b).hexdigest(),len(b)
def check(p,e):
 assert digest(p)==(e['sha256'],e.get('size',e.get('bytes'))), 'binding mismatch: '+str(p)
def payload(base,m,extra=None):
 expected={x['path'] for x in m['files']}
 actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
 if extra:actual.add(extra)
 assert actual-set(m['excluded_exact_paths'])==expected, 'exact file set mismatch'
 for e in m['files']:check(base/e['path'],e)
def main():
 m=load(O/'manifest.json');payload(O,m)
 for n in ['flat-bindings.json','initial-bindings.json','derivative-bindings.json','source-provenance.json']:
  for e in load(O/n):check(e['path'],e)
 im=load(I/'manifest.json');payload(I,im)
 pairs=load(I/'bindings.json')
 for e in pairs:
  check(e['original'],e);check(e['copy'],e)
 inv=load(R/'manifest.json')
 inventory_bindings=[e for e in pairs if e['original']==str(R/'manifest.json')]
 assert len(inventory_bindings)==1
 check(R/'manifest.json',inventory_bindings[0])
 chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert digest(R/'frozen'/n)==digest(O.parent/'root-mathdb-accepted-exclusions-r304'/n)
 cov=load(I/'coverage-delta.json');assert len(cov)==7933
 reservations=load(I/'active-breadth-reservations.json');sets=[set(r['ids']) for r in reservations]
 assert len(sets)==3
 for j,a in enumerate(sets):
  assert len(a)==50 and not a&set(map(int,cov)) and not a&set(reservations[j]['protected_ids'])
  for b in sets[j+1:]:assert not a&b
 reservation=load(I/'reserved-ids-r680.json');ids=set(reservation['ids'])
 assert len(ids)==50 and ids=={r['mathdb_id'] for r in load(I/'queue-r680.json')}
 assert ids in sets and not ids&set(reservation['protected_ids']) and not ids&set(reservation['active_hypothesis_ids'])
 assert set(load(I/'reserved-ids-r682.json')['ids']) in sets
 rows=load(O/'literal-records.json');disps=load(O/'dispositions.json')
 assert len(rows)==len(disps)==50 and {x['mathdb_id'] for x in disps}==ids
 byid={x['mathdb_id']:x for x in disps};seen=set()
 wanted={r['chunk']:{x['line']:x for x in rows if x['chunk']==r['chunk']} for r in rows}
 for path,lines in wanted.items():
  assert path in {str(R/e['path']) for e in chunks}
  for no,line in enumerate(Path(path).open(),1):
   if no not in lines:continue
   x=lines[no];v=json.loads(line);assert v==x['record']
   i=v['mathdb_id'];assert i in ids and i not in seen;seen.add(i);d=byid[i]
   h=hashlib.sha256(json.dumps(v,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
   assert h==x['canonical_record_sha256']==d['canonical_record_sha256']
   assert d['statement']==v['statement'] and d['statement_utf8_sha256']==hashlib.sha256(v['statement'].encode()).hexdigest()
   assert d['chunk']==path and d['line']==no
   assert d['completeness_classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
   assert d['completeness_reason'] and d['quantifiers_and_technical_assessment'] and d['accepted_credit']==0
 assert seen==ids
 proposals=load(O/'proposals.json');assert len(proposals)<=3 and not proposals
 negatives=[]
 if '--negative-tests' in sys.argv:
  for kind in ['sha256','size','extra-file']:
   bad=copy.deepcopy(m)
   if kind=='sha256':bad['files'][0]['sha256']='0'*64
   if kind=='size':bad['files'][0]['size']+=1
   try:payload(O,bad,'__synthetic_extra_file__' if kind=='extra-file' else None)
   except AssertionError:negatives.append(dict(test=kind,rejected=True))
   else:raise AssertionError('negative test accepted: '+kind)
 print(json.dumps(dict(integrity='PASS',math_or_novelty_pass=False,literals=50,corpus_chunks=20,frozen_inputs=8,intake_files=len(im['files']),original_copy_pairs=len(pairs),baseline=7933,proposals=len(proposals),negative_tests=negatives,manifest=dict(sha256=digest(O/'manifest.json')[0],size=digest(O/'manifest.json')[1]))))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
