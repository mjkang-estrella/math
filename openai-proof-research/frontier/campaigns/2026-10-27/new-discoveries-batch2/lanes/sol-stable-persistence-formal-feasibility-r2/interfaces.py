from audit import *
import re
before=json.loads((L/'mathlib-before.json').read_text())['files']; binds=json.loads((L/'library-bindings.json').read_text())
paths=['Mathlib/Topology/Order/Cadlag.lean','Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean','Mathlib/Probability/Kernel/Defs.lean','Mathlib/Probability/Kernel/Integral.lean','Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean','Mathlib/MeasureTheory/Measure/CharacteristicFunction/Uniqueness.lean','Mathlib/Analysis/Normed/Operator/Basic.lean','Mathlib/Topology/ContinuousMap/Bounded/Normed.lean']
for rel in paths:
 if rel not in before: continue
 p=M/rel;q=L/'library'/rel.replace('/','__');assert sha(p)==before[rel];shutil.copyfile(p,q);assert sha(q)==before[rel]
 binds.append({'original':str(p),'copy':str(q),'sha256':before[rel]})
dump('library-bindings.json',binds)
out=[]
pat=r'charFun_gaussianReal|eq_of_charFun|structure IsCadlag|isBounded_image_of_isCadlag|HasIndepIncrements|structure Kernel|def comp |integral_comp|tendsto_integral_of_dominated_convergence|tendstoUniformlyOn_of_forall_tendsto|opNorm_le_bound|norm_le |optionalStopping|optional_stopping|IsBrownian|brownianMotion|hasLaw|hasGaussianLaw'
for b in binds:
 p=pathlib.Path(b['copy'])
 if p.suffix!='.lean':continue
 lines=p.read_text().splitlines()
 for i,line in enumerate(lines):
  if re.search(pat,line) and re.search(r'\b(theorem|lemma|def|structure)\b',line):
   j=i
   while j<min(i+22,len(lines)):
    if ':=' in lines[j] or ' where' in lines[j] or (j>i and not lines[j].strip()):break
    j+=1
   out.append(str(pathlib.Path(b['original']).relative_to(M))+':'+str(i+1)+'\n'+'\n'.join(lines[i:j+1]))
(L/'interfaces.txt').write_text('\n\n'.join(out)+'\n')
print('\n\n'.join(out))
