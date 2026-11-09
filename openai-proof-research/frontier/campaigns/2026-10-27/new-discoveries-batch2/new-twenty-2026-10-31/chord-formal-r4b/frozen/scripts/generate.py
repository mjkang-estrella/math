from pathlib import Path
import itertools,json
R=Path(__file__).resolve().parent.parent
S=R/'src'
def mats(free,t=None):
 if not free:
  yield tuple(t); return
 if t is None:t=[-1]*10
 i=free[0]
 for j in free[1:]:
  tt=t[:];tt[i]=j;tt[j]=i
  yield from mats([k for k in free if k!=i and k!=j],tt)
def cross(t,a,b):return a<t[a] and b<t[b] and (a<b<t[a]<t[b] or b<a<t[b]<t[a])
def tri(t):return any(cross(t,a,b) and cross(t,a,c) and cross(t,b,c) for a,b,c in itertools.product(range(10),repeat=3))
def iso(t):return next((a for a in range(10) if a<t[a] and all(not cross(t,a,b) and not cross(t,b,a) for b in range(10))),None)
def bdy(t,m):
 N=len(t);perm=[]
 for h in range(3*N):
  i,k=divmod(h,3)
  z=3*((i-1)%N)+1 if k==0 else 3*((i+1)%N) if k==1 else 3*t[i]+2
  v,l=divmod(z,3)
  perm.append(3*v+(([2,0,1] if m>>v&1 else [1,2,0])[l]))
 seen=set();b=0
 for h in range(3*N):
  if h in seen:continue
  b+=1
  while h not in seen:seen.add(h);h=perm[h]
 return b
def transform(t,r,rev):
 e=lambda i:(r+10-1-i)%10 if rev else (i+r)%10
 out=[0]*10
 for i in range(10):out[e(i)]=e(t[i])
 return tuple(out)
target=(3,4,5,0,1,2,7,6,9,8)
M=list(mats(list(range(10))))
header='import ChordComb2Base\nnamespace Chord.Comb2\nset_option maxRecDepth 10000\nset_option maxHeartbeats 10000000\n'
# First group only while testing.
for group in range(63):
 ts=M[group*15:(group+1)*15]
 out=header
 for idx,t in enumerate(ts):
  name=f'd5_{group}_{idx}'
  out+=f'def {name} : Diagram 5 := tableDiagram (by decide) {list(t)} (by decide) (by decide)\n'
  out+=f'theorem cert5_{group}_{idx} : MaxTwo {name} → FiveProperty {name} := by\n'
  a=iso(t);eq=next(((r,v) for v in (False,True) for r in range(10) if transform(t,r,v)==target),None)
  if a is not None and (not tri(t) or eq):
   out+='  intro _\n  constructor\n'
   out+=f'  · exact ⟨{a}, by decide, by decide⟩\n'
   if not tri(t):out+=f'  · intro h\n    exact False.elim ((by decide : ¬HasTriangle {name}) h)\n'
   else:
    r,v=eq
    out+='  · intro _\n    apply Relation.EqvGen.rel\n'
    out+=f'    refine ⟨dihedral5 {r} {str(v).lower()}, ?_, ?_⟩\n'
    out+=f'    · exact {"Or.inr" if v else "Or.inl"} ⟨{r}, by decide⟩\n    · decide\n'
  else:
   mask=next(m for m in range(1024) if bdy(t,m)==1)
   out+=f'  intro h\n  have hg : genusRange {name} 3 := ⟨maskSides5 {mask}, by decide⟩\n  have := h 3 hg\n  omega\n'
 # eliminator 15 matches, input prefix equations on first2 pairs
 prefix={}
 for _ in range(2):
  i=next(k for k in range(10) if k not in prefix);j=ts[0][i];prefix[i]=j;prefix[j]=i
 params=' '.join(f'(h{i} : D.partner {i} = {j})' for i,j in prefix.items())
 out+=f'theorem cases5_{group} (P : Diagram 5 → Prop)\n'
 out+=''.join(f'    (c{k} : P d5_{group}_{k})\n' for k in range(15))
 out+=f'    (D : Diagram 5) {params} : P D := by\n'
 def tree(pref,indent):
  global out
  if len(pref)==10:
   idx=ts.index(tuple(pref[i] for i in range(10)))
   out+=indent+f'have hd : D = d5_{group}_{idx} := by\n'
   out+=indent+'  apply diagram_ext\n'+indent+'  funext i\n'+indent+f'  fin_cases i <;> simpa only [d5_{group}_{idx}, tableDiagram] using (by assumption : D.partner _ = _)\n'
   out+=indent+f'exact hd ▸ c{idx}\n';return
  i=next(k for k in range(10) if k not in pref)
  js=[j for j in range(i+1,10) if j not in pref]
  out+=indent+f'have opts : '+ ' ∨ '.join(f'D.partner {i} = {j}' for j in js)+' := by\n'
  out+=indent+f'  have inv := D.involutive {i}\n'+indent+f'  have nf := D.noFixed {i}\n'
  out+=indent+f'  generalize hv : D.partner {i} = v\n{indent}  fin_cases v <;> simp_all\n'
  if len(js)>1:out+=indent+'rcases opts with '+ ' | '.join(f'h{i}_{j}' for j in js)+'\n'
  for j in js:
   ind=indent+'  ' if len(js)>1 else indent
   if len(js)>1:out+=indent+'· '
   else:out+=indent+f'have h{i}_{j} := opts\n'+indent
   out+=f'have h{j} : D.partner {j} = {i} := by simpa only [h{i}_{j}] using D.involutive {i}\n'
   pp=dict(pref);pp[i]=j;pp[j]=i
   tree(pp,ind)
 tree(prefix,'  ')
 out+='end Chord.Comb2\n'
 (S/f'ChordComb2Five{group}.lean').write_text(out)
(R/'certificate.json').write_text(json.dumps({'matchings':M,'count':len(M)}))
print('generated',len(M),'matchings in 63 chunks')
for group in range(63):
 p=S/f'ChordComb2Five{group}.lean'
 txt=p.read_text().replace('end Chord.Comb2\n','')
 pref={};t=M[15*group]
 for _ in range(2):
  i=next(k for k in range(10) if k not in pref);j=t[i];pref[i]=j;pref[j]=i
 params=' '.join(f'(h{i} : D.partner {i} = {j})' for i,j in pref.items())
 txt+=f'theorem closed5_{group} (D : Diagram 5) {params} : MaxTwo D → FiveProperty D :=\n  cases5_{group} (fun E => MaxTwo E → FiveProperty E) '+ ' '.join(f'cert5_{group}_{k}' for k in range(15))+' D '+ ' '.join(f'h{i}' for i in pref)+'\nend Chord.Comb2\n'
 p.write_text(txt)
out=''.join(f'import ChordComb2Five{g}\n' for g in range(63))+'namespace Chord.Comb2\nset_option maxHeartbeats 10000000\nset_option maxRecDepth 10000\ntheorem fiveChordLemma : FiveChordLemma := by\n  intro D\n'
def top(pref,indent):
 global out
 if len(pref)==4:
  group=next(g for g in range(63) if all(M[15*g][i]==j for i,j in pref.items()))
  out+=indent+f'exact closed5_{group} D '+ ' '.join(f'h{i}' for i in pref)+'\n';return
 i=next(k for k in range(10) if k not in pref);js=[j for j in range(i+1,10) if j not in pref]
 out+=indent+'have opts : '+' ∨ '.join(f'D.partner {i} = {j}' for j in js)+' := by\n'
 out+=indent+f'  have inv := D.involutive {i}\n'+indent+f'  have nf := D.noFixed {i}\n'
 out+=indent+f'  generalize hv : D.partner {i} = v\n'+indent+'  fin_cases v <;> simp_all\n'
 out+=indent+'rcases opts with '+' | '.join(f'h{i}_{j}' for j in js)+'\n'
 for j in js:
  out+=indent+f'· have h{i} := h{i}_{j}\n'+indent+f'  have h{j} : D.partner {j} = {i} := by simpa only [h{i}] using D.involutive {i}\n'
  pp=dict(pref);pp[i]=j;pp[j]=i;top(pp,indent+'  ')
top({},'  ')
out+='#print axioms fiveChordLemma\nend Chord.Comb2\n'
(S/'ChordComb2Five.lean').write_text(out)
entries=[]
for t in M:
 a=iso(t);eq=next(((r,v) for v in (False,True) for r in range(10) if transform(t,r,v)==target),None)
 if a is not None and (not tri(t) or eq):
  entries.append({'partners':t,'isolated_endpoint':a,'triangle':tri(t),'dihedral_to_r3block':eq})
 else:
  entries.append({'partners':t,'genus3_mask':next(m for m in range(1024) if bdy(t,m)==1)})
(R/'certificate.json').write_text(json.dumps({'count':len(M),'entries':entries,'positive':sum('isolated_endpoint' in e for e in entries),'genus3_witnesses':sum('genus3_mask' in e for e in entries)},indent=1)+'\n')
