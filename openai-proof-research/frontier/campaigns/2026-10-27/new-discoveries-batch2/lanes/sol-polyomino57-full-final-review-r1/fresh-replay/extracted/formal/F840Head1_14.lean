import F840List
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem pair1_14 : ∀ T ∈ ({} : Finset GridPoint).powersetCard 1, insert (1,-1) (insert (6,2) T) ∈ pairs.map Prod.fst := by decide
theorem head1_14 : ∀ E ∈ ({(6,2)} : Finset GridPoint).powersetCard 2, insert (1,-1) E ∈ pairs.map Prod.fst := by
  intro E hE
  have heq : ({(6,2)} : Finset GridPoint) = insert (6,2) {} := by decide
  rw [heq, show 2 = 1+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE
  rcases Finset.mem_union.mp hE with h | h
  · have hf : (∅ : Finset GridPoint).powersetCard 2 = ∅ := by decide
    rw [hf] at h
    exact False.elim (Finset.notMem_empty _ h)
  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact pair1_14 T hT
end F840
