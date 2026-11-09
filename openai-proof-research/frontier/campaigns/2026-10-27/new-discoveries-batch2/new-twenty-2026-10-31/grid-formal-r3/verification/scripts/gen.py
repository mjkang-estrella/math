from pathlib import Path
p=Path(__file__).resolve().parent.parent
def parts(a=(0,)):
 if len(a)==4: yield a;return
 for x in range(max(a)+2): yield from parts(a+(x,))
ps=list(parts())
s='''module
public import GridFinal2
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
namespace Grid343536
def codes4 : Fin 15 → Fin 4 → ℕ := ![
'''+',\n'.join('!['+', '.join(map(str,a))+']' for a in ps)+''']
theorem setoid4_complete (r : Setoid (Fin 4)) :
    ∃ i : Fin 15, r = Setoid.ker (codes4 i) := by
  classical
'''
pairs=[(i,j) for i in range(4) for j in range(i+1,4)]
def gen(ix,truth,indent):
 if ix<len(pairs):
  a,b=pairs[ix]
  return ' '*indent+f'by_cases h{a}{b} : r {a} {b}\n'+' '*indent+'·\n'+gen(ix+1,truth+[True],indent+2)+' '*indent+'·\n'+gen(ix+1,truth+[False],indent+2)
 # if inconsistent transitive use explicit proof
 rel=lambda i,j: i==j or truth[pairs.index(tuple(sorted((i,j))))]
 for i in range(4):
  for j in range(4):
   for k in range(4):
    if rel(i,j) and rel(j,k) and not rel(i,k):
     def pf(a,b):
      if a==b:return f'(r.refl {a})'
      return f'h{a}{b}' if a<b else f'(r.symm h{b}{a})'
     a,b=sorted((i,k))
     pr=f'(r.trans {pf(i,j)} {pf(j,k)})'
     if i>k:pr=f'(r.symm {pr})'
     return ' '*indent+f'exact False.elim (h{a}{b} {pr})\n'
 idx=next(n for n,v in enumerate(ps) if all((v[a]==v[b])==t for (a,b),t in zip(pairs,truth)))
 out=' '*indent+f'refine ⟨{idx}, ?_⟩\n'+' '*indent+'ext u v\n'+' '*indent+'fin_cases u <;> fin_cases v\n'
 for u in range(4):
  for v in range(4):
   a,b=sorted((u,v))
   if rel(u,v):
    pr=f'(r.refl {u})' if u==v else f'h{a}{b}' if u<v else f'(r.symm h{a}{b})'
    out+=' '*indent+f'· exact iff_of_true {pr} rfl\n'
   else:
    pr=f'h{a}{b}' if u<v else f'(fun h => h{a}{b} (r.symm h))'
    out+=' '*indent+f'· exact iff_of_false {pr} (by change ¬ (codes4 {idx} {u} = codes4 {idx} {v}); decide)\n'
 return out
s+=gen(0,[],2)+'end Grid343536\n'
(p/'src/GridFiniteCodes.lean').write_text(s)
