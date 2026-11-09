from pathlib import Path
import gzip,json,os,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
pair=lambda p:f'({p[0]},{p[1]})'
def fs(ps):return '{'+','.join(map(pair,ps))+'}' if ps else '∅'
def tree(vals,x):
 if len(vals)==1:return str(vals[0])
 m=len(vals)//2
 return f'(if {x} < {m} then {tree(vals[:m],x)} else {tree(vals[m:],f"({x}-{m})")})'
def data(a,b,e):
 cells=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b],key=lambda p:(sum(p),p[0]-p[1]))
 centers=[(x,y) for x in range(-10,12) for y in range(-10,12) if a-5<=x+y<=5 and e+b-5<=x-y<=e+5]
 holes={(2,2),(2,-2),(-2,2),(-2,-2)}
 groups={sum(1<<i for i,(x,y) in enumerate(cells) if (x-cx,y-cy) in holes) for cx,cy in centers}
 groups.update(sum(1<<i for i,(x,y) in enumerate(cells) if f(x,y)==bound) for f,bound in [(lambda x,y:x+y,0),(lambda x,y:x+y,a),(lambda x,y:x-y,e),(lambda x,y:x-y,e+b)])
 gs=sorted([g for g in groups if not any(h!=g and h&g==h for h in groups)],key=lambda g:[i for i in range(len(cells)) if g>>i&1])
 return cells,gs
cells,gs=data(10,10,1);n=len(cells);k=len(gs);raw=gzip.decompress((L/'inputs/compression/steiner-10-10-1.bin.gz').read_bytes())
header='''import FiniteBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57
'''
s=header+f'def point (i : Fin {n}) : GridPoint := '+tree([pair(p) for p in cells],'i.val')+'\n'
s+=f'def group (i : Fin {k}) : Finset GridPoint := '+tree([fs([p for j,p in enumerate(cells) if g>>j&1]) for g in gs],'i.val')+'\n'
s+=f'def mask (A : Finset (Fin {k})) : ℕ := '+ ' + '.join(f'(if ({i} : Fin {k}) ∈ A then {1<<i} else 0)' for i in range(k))+'\n'
s+=f'def value (A : Finset (Fin {k})) (i : Fin {n}) : ℕ := '+tree([tree(list(raw[m*n:(m+1)*n]),'i.val') for m in range(1<<k)],'mask A')+'\n'
s+='end Polyomino57.Diagonal.FiniteProof.Small\n'
(L/'formal/SmallData.lean').write_text(s)
# independent stages so a bounded failure doesn't hide earlier proofs
stages={
'SmallGeometry':f'''theorem domain_eq : domain 10 10 1 = (Finset.univ : Finset (Fin {n})).image point := by decide
theorem point_injective : Function.Injective point := by
  intro i j
  have h : ∀ i j : Fin {n}, point i = point j → i = j := by decide
  exact h i j
theorem groups_mem : ∀ i ∈ (Finset.univ : Finset (Fin {k})), group i ∈ groups 10 10 1 := by decide
''',
'SmallBase':f'''theorem base_check : ∀ A ∈ (Finset.univ : Finset (Fin {k})).powerset, A.Nonempty → ∀ z : Fin {n}, z ∈ Finset.univ →
 (∀ i ∈ A, point z ∈ group i) → value A z ≤ 1 := by decide
''',
'SmallEdge':f'''theorem edge_check : ∀ A ∈ (Finset.univ : Finset (Fin {k})).powerset, A.Nonempty → ∀ z : Fin {n}, z ∈ Finset.univ → ∀ w : Fin {n}, w ∈ Finset.univ →
 Adj (point z) (point w) → value A z ≤ value A w + 1 := by decide
''',
'SmallMerge':f'''theorem merge_check : ∀ A ∈ (Finset.univ : Finset (Fin {k})).powerset, ∀ B ∈ (Finset.univ : Finset (Fin {k})).powerset, A.Nonempty → B.Nonempty → Disjoint A B → ∀ z : Fin {n}, z ∈ Finset.univ →
 value (A ∪ B) z + 1 ≤ value A z + value B z := by decide
''',
'SmallFull':f'''theorem full_check : ∀ z : Fin {n}, z ∈ Finset.univ → 12 ≤ value Finset.univ z := by decide
'''}
for name,body in stages.items():(L/'formal'/f'{name}.lean').write_text(header.replace('import FiniteBridge','import SmallData')+body+'end Polyomino57.Diagonal.FiniteProof.Small\n')
for p in (L/'formal').glob('Small*.lean'):(L/'dev'/p.name).write_bytes(p.read_bytes())
