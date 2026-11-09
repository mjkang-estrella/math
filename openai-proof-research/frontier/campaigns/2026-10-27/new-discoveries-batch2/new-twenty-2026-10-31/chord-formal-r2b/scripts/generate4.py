from pathlib import Path
import itertools,json
R=Path(__file__).resolve().parent.parent;S=R/'src'
def mats(free,t=None):
 if t is None:t=[-1]*8
 if not free:yield tuple(t);return
 i=free[0]
 for j in free[1:]:
  tt=t[:];tt[i]=j;tt[j]=i
  yield from mats([k for k in free if k!=i and k!=j],tt)
def bdy(t,m):
 N=len(t);perm=[]
 for h in range(3*N):
  i,k=divmod(h,3)
  z=3*((i-1)%N)+1 if k==0 else 3*((i+1)%N) if k==1 else 3*t[i]+2
  v,l=divmod(z,3);perm.append(3*v+(([2,0,1] if m>>v&1 else [1,2,0])[l]))
 seen=set();b=0
 for h in range(3*N):
  if h in seen:continue
  b+=1
  while h not in seen:seen.add(h);h=perm[h]
 return b
def transform(t,r,rev):
 e=lambda i:(r+8-1-i)%8 if rev else (i+r)%8
 out=[0]*8
 for i in range(8):out[e(i)]=e(t[i])
 return tuple(out)
# literal frozen exceptional representatives
reps=[]
for w in ['11234234','12134234','12314234','12341234']:
 reps.append(tuple(next(j for j in range(8) if j!=i and w[j]==w[i]) for i in range(8)))
M=list(mats(list(range(8))))
for group in range(7):
 ts=M[group*15:(group+1)*15]
 out='import ChordComb2OrbitFour\nnamespace Chord.Comb2\nset_option maxRecDepth 10000\nset_option maxHeartbeats 10000000\n'
 for idx,t in enumerate(ts):
  name=f'd4_{group}_{idx}'
  out+=f'def {name} : Diagram 4 := tableDiagram (by decide) {list(t)} (by decide) (by decide)\n'
  out+=f'theorem cert4_{group}_{idx} : Range12 {name} → ∃ i, Equivalent {name} (fourReps i) := by\n'
  eq=next(((k,r,v) for k in range(4) for v in (False,True) for r in range(8) if transform(t,r,v)==reps[k]),None)
  if eq:
   k,r,v=eq
   out+=f'  intro _\n  refine ⟨{k}, Relation.EqvGen.rel _ _ (orbit4_generator ?_)⟩\n  exact ⟨{r}, {str(v).lower()}, by decide⟩\n'
  else:
   mask=next(m for m in range(256) if bdy(t,m)==6)
   out+=f'  intro h\n  have hg : genusRange {name} 0 := ⟨maskSides 4 {mask}, by decide⟩\n  have := (h 0).mp hg\n  omega\n'
 prefix={0:group+1,group+1:0}
 params=' '.join(f'(h{i} : D.partner {i} = {j})' for i,j in prefix.items())
 out+=f'theorem cases4_{group} (P : Diagram 4 → Prop)\n'+''.join(f'    (c{k} : P d4_{group}_{k})\n' for k in range(15))+f'    (D : Diagram 4) {params} : P D := by\n'
 def tree(pref,indent):
  global out
  if len(pref)==8:
   idx=ts.index(tuple(pref[i] for i in range(8)))
   out+=indent+f'have hd : D = d4_{group}_{idx} := by\n'+indent+'  apply diagram_ext\n'+indent+'  funext i\n'+indent+f'  fin_cases i <;> simpa only [d4_{group}_{idx}, tableDiagram] using (by assumption : D.partner _ = _)\n'+indent+f'exact hd ▸ c{idx}\n';return
  i=next(k for k in range(8) if k not in pref);js=[j for j in range(i+1,8) if j not in pref]
  out+=indent+'have opts : '+' ∨ '.join(f'D.partner {i} = {j}' for j in js)+' := by\n'+indent+f'  have inv := D.involutive {i}\n'+indent+f'  have nf := D.noFixed {i}\n'+indent+f'  generalize hv : D.partner {i} = v\n'+indent+'  fin_cases v <;> simp_all\n'
  if len(js)>1:out+=indent+'rcases opts with '+' | '.join(f'h{i}_{j}' for j in js)+'\n'
  for j in js:
   ind=indent+'  ' if len(js)>1 else indent
   if len(js)>1:out+=indent+'· '
   else:out+=indent+f'have h{i}_{j} := opts\n'+indent
   out+=f'have h{j} : D.partner {j} = {i} := by simpa only [h{i}_{j}] using D.involutive {i}\n'
   pp=dict(pref);pp[i]=j;pp[j]=i;tree(pp,ind)
 tree(prefix,'  ')
 out+=f'theorem closed4_{group} (D : Diagram 4) {params} : Range12 D → ∃ i, Equivalent D (fourReps i) :=\n  cases4_{group} (fun E => Range12 E → ∃ i, Equivalent E (fourReps i)) '+' '.join(f'cert4_{group}_{k}' for k in range(15))+' D '+ ' '.join(f'h{i}' for i in prefix)+'\nend Chord.Comb2\n'
 (S/f'ChordComb2Four{group}.lean').write_text(out)
out=''.join(f'import ChordComb2Four{g}\n' for g in range(7))+'namespace Chord.Comb2\nset_option maxHeartbeats 10000000\nset_option maxRecDepth 10000\ntheorem four_complete (D : Diagram 4) : Range12 D → ∃ i, Equivalent D (fourReps i) := by\n  have opts : '+' ∨ '.join(f'D.partner 0 = {j}' for j in range(1,8))+' := by\n    have inv := D.involutive 0\n    have nf := D.noFixed 0\n    generalize hv : D.partner 0 = v\n    fin_cases v <;> simp_all\n  rcases opts with '+' | '.join(f'h{j}' for j in range(1,8))+'\n'
for j in range(1,8):out+=f'  · exact closed4_{j-1} D h{j} (by simpa only [h{j}] using D.involutive 0)\n'
out+='theorem fourChordEnumeration : FourChordEnumeration := ⟨fourReps, fourReps_range, fourReps_distinct, four_complete⟩\n#print axioms fourChordEnumeration\nend Chord.Comb2\n'
(S/'ChordComb2Four.lean').write_text(out)
print('generated 105 four-chord cases in 7 chunks')
