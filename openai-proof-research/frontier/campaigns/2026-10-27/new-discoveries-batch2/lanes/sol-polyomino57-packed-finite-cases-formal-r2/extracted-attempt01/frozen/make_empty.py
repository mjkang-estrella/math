from pathlib import Path
import json,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
rs=json.loads((L/'inputs/compression/verification.json').read_text())['receipts']
empty=[r for r in rs if r['verified']=='empty-constraint']
for ix,r in enumerate(empty):
 a,b,e=[r[k] for k in ['a','b','e']]
 # Use an explicit collision-center witness to avoid computing giant finite groups.
 centers=[(s,t) for s in range(a-5,6) for t in range(e+b-5,e+6) if (s-t)%2==0]
 cells=[(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b]
 s,t=next((s,t) for s,t in centers if not any((x+y-s,x-y-t) in [(4,0),(-4,0),(0,4),(0,-4)] for x,y in cells))
 text=f'''import FiniteBridge
set_option autoImplicit false
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
theorem empty_{a}_{b}_{e} : ∅ ∈ groups {a} {b} {e} := by
  have hc : ({s},{t}) ∈ centers {a} {b} {e} := by decide
  have hg : collisionGroup {a} {b} {e} ({s},{t}) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hd := (mem_domain (by omega) (by omega) (by omega) p).mp
      ((mem_collisionGroup {a} {b} {e} ({s},{t}) p).mp hp).1
    have hh := ((mem_collisionGroup {a} {b} {e} ({s},{t}) p).mp hp).2
    dsimp [Collision,u,v] at *
    omega
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨({s},{t}),hc,rfl⟩)
theorem case_{a}_{b}_{e} : ∀ Q : Finset GridPoint, Q ⊆ domain {a} {b} {e} →
    EdgeConnected Q → Q.card = 11 → ¬ HitsAll Q (groups {a} {b} {e}) := by
  intro Q _ _ _
  exact empty_group_impossible empty_{a}_{b}_{e}
end Polyomino57.Diagonal.FiniteProof
'''
 name=f'Empty{ix:02}'
 (L/'formal'/f'{name}.lean').write_text(text);(L/'dev'/f'{name}.lean').write_text(text)
(L/'empty-cases.json').write_text(json.dumps(empty,indent=2)+'\n')
