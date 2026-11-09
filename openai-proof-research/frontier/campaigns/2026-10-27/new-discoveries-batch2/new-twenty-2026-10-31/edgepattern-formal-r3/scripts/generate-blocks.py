from pathlib import Path
from itertools import product
import json
mods=[]
for a,b,c,d in product(range(3),repeat=4):
 tag=f'{a}{b}{c}{d}'; k=f'⟨{a},{b},{c},{d}⟩'
 edges=[(0,1),(0,2),(0,3),(1,4),(1,5)]; n=6
 for parent,num in zip([2,3,4,5],[a,b,c,d]):
  edges += [(parent,i) for i in range(n,n+num)]; n+=num
 good=[m for m in range(2**n) if all(not (m>>x&1 and m>>y&1) for x,y in edges)]
 M=max(m.bit_count() for m in good); ms=[m for m in good if m.bit_count()==M]; literal='{'+','.join(map(str,ms))+'}'
 L=min(256,2**n); B=2**n//L
 imports=[]
 for group in range((B+3)//4):
  name=f'ChecksR3_{tag}_{group}';imports.append(name);mods.append(name)
  s='import TreeModelsR3\nnamespace EdgePattern.TreeModelsR3\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
  for block in range(group*4,min(B,group*4+4)):
   s+=f'theorem check_{tag}_{block} : MaskR3.blockCheck (graph {k}) {M} {literal} {block*L} {L} := by decide\n'
  s+='end EdgePattern.TreeModelsR3\n';Path('formal',name+'.lean').write_text(s)
 totals=[sum(sum(1 for x in range(n) if (m>>x&1) and (0 if x<2 else 1 if x<6 else 2)==i) for m in ms) for i in range(3)]
 s=''.join(f'import {name}\n' for name in imports)+f'''namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_{tag} : MaskR3.best (graph {k}) = {literal} := by
  apply MaskR3.best_of_checks (graph {k}) {M} {literal} (by decide) (by decide)
  have hall : ∀ b : Fin {B}, MaskR3.blockCheck (graph {k}) {M} {literal} (b.val * {L}) {L} := by
    intro b
    fin_cases b
'''
 s+='\n'.join(f'    · exact check_{tag}_{block}' for block in range(B))+'\n'
 s+=f'''  intro m hm ho
  change m < {2**n} at hm
  let b : Fin {B} := ⟨m / {L}, by omega⟩
  let i : Fin {L} := ⟨m % {L}, by omega⟩
  have he : b.val * {L} + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_{tag} : totals {k} 0 = {totals[0]} ∧ totals {k} 1 = {totals[1]} ∧ totals {k} 2 = {totals[2]} := by
  unfold totals
  rw [best_{tag}]
  decide
theorem count_{tag} : count {k} = {len(ms)} := by
  unfold count
  rw [best_{tag}]
  decide
theorem bound_{tag} : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy {k} i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_{tag}.1, totals_{tag}.2.1, totals_{tag}.2.2, count_{tag}]
end EdgePattern.TreeModelsR3
'''
 Path('formal',f'EvalR3_{tag}.lean').write_text(s);mods.append(f'EvalR3_{tag}')
Path('scripts/eval-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
print('Generated',len(mods),'modules')
