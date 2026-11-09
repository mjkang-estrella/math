from pathlib import Path
import json
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
def head(i):return N[i] if isinstance(N[i],str) else head(N[i][0])
clips=[];seen=set()
def visit(i):
 if i in seen:return
 seen.add(i)
 if isinstance(N[i],str):return
 if head(i)=='ite':
  p,t,f=N[i][1:];assert N[t]=='0' and head(f)=='ite',(i,N[i])
  z=N[p][1];q,hh,zz=N[f][1:];assert z==zz and N[hh]=='H'
  clips.append((i,z,p,f,q));return
 for j in N[i][1:]:visit(j)
visit(11660)
lines=['import Query','import Reduction','import Mathlib.Tactic.SplitIfs','set_option autoImplicit false','set_option warningAsError true','namespace Assembly',
'theorem clip_ite (H : ℕ) (z : ℤ) : FloorSums.clip H z = (if z ≤ 0 then 0 else if z ≥ (H : ℤ) then (H : ℤ) else z) := by',
'  unfold FloorSums.clip','  simp only [max_def, min_def]','  split_ifs <;> omega']
for i,z,p,f,q in clips:
 lines += [f'theorem clip_{i} (v : Vars) (H : ℕ) (hH : v.H = (H : ℤ)) : e{i} v = FloorSums.clip H (e{z} v) := by',f'  unfold e{i} e{p} e{f} e{q} e12 e17', '  rw [hH]', '  exact (clip_ite H _).symm']
lines+=['end Assembly'];(L/'ClipBridge.lean').write_text('\n'.join(lines)+'\n')
(L/'clip-inventory.json').write_text(json.dumps(clips,indent=2)+'\n')
print('query clip bodies',len(clips))
