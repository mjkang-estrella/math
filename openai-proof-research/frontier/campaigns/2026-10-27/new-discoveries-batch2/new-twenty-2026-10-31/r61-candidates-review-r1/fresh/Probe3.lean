import CaterpillarCenter
open SimpleGraph Finset Caterpillar366834
namespace Probe
def edges28 : List (Fin 28 × Fin 28) := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,6),(1,7),(1,8),(1,9),(1,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(3,17),(3,18),(3,19),(3,20),(3,21),(5,22),(5,23),(5,24),(5,25),(5,26),(5,27)]
def T : SimpleGraph (Fin 28) where
  Adj a b := (a, b) ∈ edges28 ∨ (b, a) ∈ edges28
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩
instance : DecidableRel T.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges28 ∨ (b, a) ∈ edges28))
-- leaf 27 (attached to spine vertex 5); expected value from Python
theorem probe : ((powersetCard 3 univ).filter fun s : Finset (Fin 28) => T.IsIndepSet (s : Set (Fin 28)) ∧ (27 : Fin 28) ∈ s).card = 305 := by
  decide +kernel
end Probe
