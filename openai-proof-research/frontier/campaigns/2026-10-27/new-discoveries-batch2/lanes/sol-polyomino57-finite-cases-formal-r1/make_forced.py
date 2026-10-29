from pathlib import Path
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent
a,b,e=7,3,0
cells=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b])
centers=[(s,t) for s in range(a-5,6) for t in range(e+b-5,e+6) if (s-t)%2==0]
forced={}
for s,t in centers:
 hit=[(x,y) for x,y in cells if (x+y-s,x-y-t) in [(4,0),(-4,0),(0,4),(0,-4)]]
 if len(hit)==1:forced[hit[0]]=(s,t)
pair=lambda p:f'({p[0]},{p[1]})'
s='''import FiniteBridge
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof
open Polyomino57
'''
for j,(p,c) in enumerate(sorted(forced.items())):
 s+=f'''theorem forced_single{j} : ({{{pair(p)}}} : Finset GridPoint) ∈ groups 7 3 0 := by
  have hc : {pair(c)} ∈ centers 7 3 0 := by decide
  have hg : collisionGroup 7 3 0 {pair(c)} = {{{pair(p)}}} := by decide
  rw [← hg]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨{pair(c)},hc,rfl⟩)
'''
s+='def forced : Finset GridPoint := {'+','.join(pair(p) for p in sorted(forced))+'}\n'
s+='''theorem forced_sub {Q : Finset GridPoint} (hh : HitsAll Q (groups 7 3 0)) : forced ⊆ Q := by
  intro p hp
  have h : ∀ p ∈ forced, ({p} : Finset GridPoint) ∈ groups 7 3 0 := by
    intro p hp
    simp only [forced, Finset.mem_insert, Finset.mem_singleton] at hp
'''
# use rcases nested disjunction
s+='    rcases hp with '+ ' | '.join(['rfl']*len(forced))+'\n'
for j in range(len(forced)):s+=f'    · exact forced_single{j}\n'
s+='''  obtain ⟨q,hq,hqp⟩ := hh {p} (h p hp)
  have he : q = p := Finset.mem_singleton.mp hqp
  exact he ▸ hq
theorem case_7_3_0 : ∀ Q : Finset GridPoint, Q ⊆ domain 7 3 0 → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups 7 3 0) := by
  intro Q _ _ hn hh
  have h := Finset.card_le_card (forced_sub hh)
  have hf : forced.card = 16 := by decide
  omega
end Polyomino57.Diagonal.FiniteProof
'''
(L/'formal/Forced730.lean').write_text(s);(L/'dev/Forced730.lean').write_text(s)
