from pathlib import Path
R=Path(__file__).resolve().parent.parent;S=R/'src'
def mats(free,t=None):
 if t is None:t=[-1]*6
 if not free:yield tuple(t);return
 i=free[0]
 for j in free[1:]:
  tt=t[:];tt[i]=j;tt[j]=i
  yield from mats([k for k in free if k!=i and k!=j],tt)
M=list(mats(list(range(6))))
out='import ChordComb2Base\nnamespace Chord.Comb2\nset_option maxRecDepth 10000\nset_option maxHeartbeats 10000000\n'
for k,t in enumerate(M):
 out+=f'def d3_{k} : Diagram 3 := tableDiagram (by decide) {list(t)} (by decide) (by decide)\n'
 out+=f'theorem tri3_{k} : HasTriangle d3_{k} → d3_{k} = r3Block 3 (by decide) := by\n'
 if t==(3,4,5,0,1,2):out+='  intro _\n  apply diagram_ext\n  decide\n'
 else:out+=f'  intro h\n  exact False.elim ((by decide : ¬HasTriangle d3_{k}) h)\n'
out+='theorem triangle_three (D : Diagram 3) : HasTriangle D → D = r3Block 3 (by decide) := by\n'
def tree(pref,indent):
 global out
 if len(pref)==6:
  k=M.index(tuple(pref[i] for i in range(6)))
  out+=indent+f'have hd : D = d3_{k} := by\n'+indent+'  apply diagram_ext\n'+indent+'  funext i\n'+indent+f'  fin_cases i <;> simpa only [d3_{k}, tableDiagram] using (by assumption : D.partner _ = _)\n'+indent+f'exact hd ▸ tri3_{k}\n';return
 i=next(k for k in range(6) if k not in pref);js=[j for j in range(i+1,6) if j not in pref]
 out+=indent+'have opts : '+' ∨ '.join(f'D.partner {i} = {j}' for j in js)+' := by\n'+indent+f'  have inv := D.involutive {i}\n'+indent+f'  have nf := D.noFixed {i}\n'+indent+f'  generalize hv : D.partner {i} = v\n'+indent+'  fin_cases v <;> simp_all\n'
 if len(js)>1:out+=indent+'rcases opts with '+' | '.join(f'h{i}_{j}' for j in js)+'\n'
 for j in js:
  ind=indent+'  ' if len(js)>1 else indent
  if len(js)>1:out+=indent+'· '
  else:out+=indent+f'have h{i}_{j} := opts\n'+indent
  out+=f'have h{j} : D.partner {j} = {i} := by simpa only [h{i}_{j}] using D.involutive {i}\n'
  pp=dict(pref);pp[i]=j;pp[j]=i;tree(pp,ind)
tree({},'  ')
out+='theorem triangleRigidity_three (D : Diagram 3) (h : HasTriangle D) : Equivalent D (r3Block 3 (by decide)) := by\n  rw [triangle_three D h]\n  exact Relation.EqvGen.refl _\nend Chord.Comb2\n'
(S/'ChordComb2Three.lean').write_text(out)
print('generated n=3 triangle rigidity, 15 matchings')
# Turn the exhaustive proof into a reusable universal eliminator as well.
p=S/'ChordComb2Three.lean';txt=p.read_text()
start=txt.index('theorem triangle_three');end=txt.index('theorem triangleRigidity_three')
body=txt[start:end]
body=body.replace('theorem triangle_three (D : Diagram 3) : HasTriangle D → D = r3Block 3 (by decide) := by', 'theorem cases3 (P : Diagram 3 → Prop)\n'+''.join(f'    (c{k} : P d3_{k})\n' for k in range(15))+'    (D : Diagram 3) : P D := by')
for k in range(15):body=body.replace(f'exact hd ▸ tri3_{k}\n',f'exact hd ▸ c{k}\n')
tri='theorem triangle_three (D : Diagram 3) : HasTriangle D → D = r3Block 3 (by decide) :=\n  cases3 (fun E => HasTriangle E → E = r3Block 3 (by decide)) '+' '.join(f'tri3_{k}' for k in range(15))+' D\n'
txt=txt[:start]+body+tri+txt[end:]
# Independent ribbon cycle implementation for genus-zero countercertificates.
def faces(t,m):
 p=[]
 for h in range(18):
  i,k=divmod(h,3)
  x=3*((i-1)%6)+1 if k==0 else 3*((i+1)%6) if k==1 else 3*t[i]+2
  v,l=divmod(x,3);p.append(3*v+([2,0,1] if m>>v&1 else [1,2,0])[l])
 seen=set();b=0
 for i in range(18):
  if i in seen:continue
  b+=1
  while i not in seen:seen.add(i);i=p[i]
 return b
txt=txt.replace('end Chord.Comb2\n','')
for k,t in enumerate(M):
 txt+=f'theorem range3_{k} : Range12 d3_{k} → d3_{k} = r3Block 3 (by decide) := by\n'
 if t==(3,4,5,0,1,2):txt+='  intro _\n  apply diagram_ext\n  decide\n'
 else:
  m=next(m for m in range(64) if faces(t,m)==5)
  txt+=f'  intro h\n  have hg : genusRange d3_{k} 0 := ⟨maskSides 3 {m}, by decide⟩\n  have := (h 0).mp hg\n  omega\n'
txt+='theorem range_three_complete (D : Diagram 3) : Range12 D → D = r3Block 3 (by decide) :=\n  cases3 (fun E => Range12 E → E = r3Block 3 (by decide)) '+' '.join(f'range3_{k}' for k in range(15))+' D\n'
txt+='theorem exactly_one_three : ExactlyClasses 3 1 := by\n  refine ⟨fun _ => r3Block 3 (by decide), fun _ => genusRange_r3, ?_, ?_⟩\n  · intro i j _\n    exact Subsingleton.elim i j\n  · intro D h\n    refine ⟨0, ?_⟩\n    rw [range_three_complete D h]\n    exact Relation.EqvGen.refl _\nend Chord.Comb2\n'
p.write_text(txt)
