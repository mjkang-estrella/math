import json,hashlib,datetime
from pathlib import Path
from fractions import Fraction
here=Path(__file__).resolve().parent
B=here.parent.parent
cwd=B.parents[4]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
adopt={'utc':stamp,'status':'FULL_ORDINARY_CANDIDATE__INDEPENDENT_REVIEW_PENDING','credit':0,'counts':[7,37],'source':'Bensmail et al., arXiv2511.14514v1 Conjecture1; HAL05548898v1 author conference manuscript, not publisher-certified PDF','root_math':'All-t charging proof rederived: two diamond deletions for each boundary bit; one length-three-path deletion; disjoint edge accounting; explicit 3t deletion set valid t>=2. Thus excess t/3 unbounded.','root_validation':json.loads((here/'root-check.json').read_text()),'source_read':'Actual HAL text definitions and Conjecture1; no regularity assumption. Prior DMTCS Section4 Claim1 inspected: larger bipartite hardness gadget, not yet established subsumer.','holds':['independent adversarial review','substantive and bounded novelty','publisher-version comparison qualification','current registry freshness','literal Lean','paper and replay'],'review_lane':'sol-edge-irregulator-preliminary-review-r1'}
(here/'ADOPTION.json').write_text(json.dumps(adopt,indent=2)+'\n')
for n in (71,72):
 src=B/'lanes'/f'sol-fresh-source-discovery-r{n}'
 out=B/'lanes'/f'root-fresh-source-r{n}-handback';out.mkdir(exist_ok=True)
 p=json.loads((src/'provenance.json').read_text()); verified={}; historical_mismatches=[]
 def walk(obj):
  if isinstance(obj,dict):
   name=obj.get('file'); h=obj.get('sha256')
   if isinstance(name,str) and isinstance(h,str) and (src/name).is_file():
    actual=sha(src/name)
    if actual==h: verified[name]=h
    else: historical_mismatches.append({'file':name,'recorded':h,'current':actual,'utc':obj.get('utc')})
   for name,h in obj.items():
    if isinstance(h,str) and len(h)==64 and (src/name).is_file():
     actual=sha(src/name)
     if actual==h: verified[name]=h
     else: historical_mismatches.append({'file':name,'recorded':h,'current':actual,'kind':'manifest'})
   for v in obj.values(): walk(v)
  elif isinstance(obj,list):
   for v in obj: walk(v)
 walk(p)
 frozen={str(f.relative_to(src)):sha(f) for f in sorted(src.rglob('*')) if f.is_file() and '__pycache__' not in f.parts}
 if n==71:
  reachable={0}
  for k in range(1,70):
   if any(k-g in reachable for g in (5,8,11,14)): reachable.add(k)
  gaps=set(range(70))-reachable; F=max(gaps)
  assert F==17 and all((k in reachable)!=(F-k in reachable) for k in range(F+1))
  assert 2*8==5+11==16
  diagnostic={'symmetric_semigroup':[5,8,11,14],'frobenius':F,'nonunique_factorization':16}
  gap='Uniform uniqueness h prime equals h in the full determinantal numerical-semigroup conjecture remains missing.'
 else:
  assert Fraction(2)<Fraction(169,81)
  diagnostic={'radical_certificate':'2 < 169/81 verified exactly; no full interpolation identity or moment scan replayed'}
  gap='Full oscillatory Mellin-integral nonnegativity for all unit-variance Rademacher vectors and 2<p<3 remains missing.'
 receipt={'utc':stamp,'status':'UNRESOLVED_PRESERVED','credit':0,'counts':[7,37],'gap':gap,'root_scope':'Read terminal handoff and SUMMARY; limited exact diagnostic and source hash checks only; not independent full mathematical/source review.','root_diagnostic':diagnostic,'verified_source_records':len(verified),'source_hashes':verified,'all_file_hashes':frozen,'holds':['registry freshness','reported source-access limits'],'worker_reported_checks_not_root_replayed':True}
 receipt['historical_hash_mismatches']=historical_mismatches
 if historical_mismatches:
  receipt['qualification']='Earlier retrieval hash may describe overwritten challenge-response bytes; do not claim every historical retrieval is preserved. r72 Pinelis1994.pdf is HTML challenge, NOT source body; repeated challenge retrieval and overwrite retained as provenance deviation. Root first verification assertion failed on that historical record; final current inventory separately bound.'
 (out/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(n,len(frozen),len(verified),diagnostic)
nextfile=B/'NEXT.md';text=nextfile.read_text()
old='Three fresh Sol high/default research lanes r70 finite structures, r72 analysis,\nr71 arithmetic/algebra are active; no children. Keep exclusions and actual source\nscopes, and do not equate Blueprint markdown trees with actual Lean trees.'
new='r70 supplies a complete ordinary connected edge-irregulator refutation: 8t edges\nand exactly3t deletions. Root charging proof and exact checks pass; independent\nreview in sol-edge-irregulator-preliminary-review-r1 is pending. Credit0.\nr71 determinantal semigroups and r72 Zinn doubling remain unresolved; limited\nroot handbacks preserve their gaps and freshness/access holds.\nActive Sol high/default: edge-irregulator review, fresh arithmetic/algebra r73,\nand fresh analysis r74. No children. Do not equate Blueprint and Lean trees.'
assert old in text or new in text
if old in text: nextfile.write_text(text.replace(old,new,1))
for n,outname in ((70,here.name),(71,'root-fresh-source-r71-handback'),(72,'root-fresh-source-r72-handback')):
 out=B/'lanes'/outname
 paths=[]
 for folder in (B/'lanes'/f'sol-fresh-source-discovery-r{n}',out):
  paths += [str(f.relative_to(cwd)) for f in sorted(folder.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name!='pathspec.txt']
 if n==70: paths.append(str(nextfile.relative_to(cwd)))
 (out/'pathspec.txt').write_text('\n'.join(paths)+'\n')
