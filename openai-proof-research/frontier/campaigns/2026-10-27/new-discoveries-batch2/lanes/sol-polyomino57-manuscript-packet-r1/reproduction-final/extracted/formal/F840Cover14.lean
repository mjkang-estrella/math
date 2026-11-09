import F840List
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem head14 : ∀ E ∈ ({} : Finset GridPoint).powersetCard 2, insert (6,2) E ∈ pairs.map Prod.fst := by decide
theorem cover14 : ∀ E ∈ ({(6,2)} : Finset GridPoint).powersetCard 3, E ∈ pairs.map Prod.fst := by
  intro E hE
  have heq : ({(6,2)} : Finset GridPoint) = insert (6,2) {} := by decide
  rw [heq, show 3 = 2+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE
  rcases Finset.mem_union.mp hE with h | h
  · have hf : (∅ : Finset GridPoint).powersetCard 3 = ∅ := by decide
    rw [hf] at h
    exact False.elim (Finset.notMem_empty _ h)
  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact head14 T hT
end F840
