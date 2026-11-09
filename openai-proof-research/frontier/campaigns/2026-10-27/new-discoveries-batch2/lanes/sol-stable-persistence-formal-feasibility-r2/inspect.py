from audit import *
import re,os
before=json.loads((L/'mathlib-before.json').read_text())['files']
patterns={
 'stable-process':r'(?i)stable.?law|stable.?distribution|symmetric.?stable|Lévy|Levy|strong.?Markov|killed|first.?passage|half.?line|half.?space',
 'support':r'(?i)maximal.*inequal|inequal.*maximal|indepIncrements|stationaryIncrements|IsMarkov|MarkovProcess|PositiveDefinite|eq_of_charFun_eq|tendsto_integral_of_dominated_convergence|tendstoUniformlyOn_of_antitone|operatorNorm|opNorm_le_bound'}
hits={k:[] for k in patterns}
selected=set()
for rel,h in before.items():
 p=M/rel; assert sha(p)==h
 s=p.read_text()
 for key,pat in patterns.items():
  for n,line in enumerate(s.splitlines(),1):
   if re.search(pat,line): hits[key].append({'file':rel,'line':n,'text':line})
  if key=='stable-process' and re.search(pat,s): selected.add(rel)
for pat in ['*Dini.lean','*DominatedConvergence.lean','*BrownianMotion/Basic.lean','*Gaussian/Real.lean','*OptionalStopping.lean','*CharacteristicFunction/Uniqueness.lean','*Kernel/Basic.lean','*Kernel/Composition/Comp.lean','*BoundedContinuousFunction/Basic.lean','*BoundedContinuousFunction/Normed.lean','*StrongLaw.lean','*Doob.lean']:
 selected.update(str(p.relative_to(M)) for p in (M/'Mathlib').glob('**/'+pat))
dump('semantic-search.json',{'patterns':patterns,'hits':hits,'coverage':'8529 Mathlib Lean source files; lexical semantic screen, not exhaustive semantic equivalence or elaboration'})
(L/'library').mkdir(exist_ok=True)
lib=[]
for rel in sorted(selected):
 p=M/rel; q=L/'library'/rel.replace('/','__'); shutil.copyfile(p,q); assert sha(p)==before[rel]==sha(q)
 lib.append({'original':str(p),'copy':str(q),'sha256':before[rel]})
dump('library-bindings.json',lib)
# Campaign source files: omit nested source snapshots, package trees and extracted historical copies.
files=[]
for root in [B/'candidates',B.parents[1]/'2026-10-14/formal']:
 for d,dirs,names in os.walk(root):
  dirs[:]=[x for x in dirs if x not in ['.lake','.git','copies','frozen','snapshots','inputs','extracted','EXTRACTED']]
  files += [pathlib.Path(d)/n for n in names if n.endswith('.lean')]
assert len(files)<10000
ch={str(p):sha(p) for p in files}; dump('campaign-before.json',ch)
out=[]
for p in files:
 assert sha(p)==ch[str(p)]
 for n,line in enumerate(p.read_text().splitlines(),1):
  if re.search(r'(?i)stable|persistence|charFun|IsCadlag|strong.?Markov|killed|Dini|dominated_convergence|weighted',line):out.append({'file':str(p),'line':n,'text':line})
dump('campaign-search.json',{'files':len(files),'roots':['batch2/candidates','2026-10-14/formal (package/snapshot exclusions)'],'hits':out})
for rel in ['primary/2608.17927v3.pdf','primary/2608.17927v3.txt','retrieval/0905.2626v4.pdf','retrieval/0905.2626v4.txt']:
 p=L.parent/'sol-stable-persistence-breadth-depth-r225'/rel; q=L/'frozen'/rel.replace('/','__'); h=sha(p);shutil.copyfile(p,q);assert sha(p)==h==sha(q)
 lib.append({'original':str(p),'copy':str(q),'sha256':h})
dump('library-bindings.json',lib)
print('Selected library files',len(selected),'campaign files',len(files),'campaign hits',len(out))
for k,v in hits.items(): print(k,len(v))
