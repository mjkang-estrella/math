import F840Head5_11
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem pair5_10 : ∀ T ∈ ({(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 1, insert (2,2) (insert (4,2) T) ∈ pairs.map Prod.fst := by decide
theorem head5_10 : ∀ E ∈ ({(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 2, insert (2,2) E ∈ pairs.map Prod.fst := by
  intro E hE
  have heq : ({(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint) = insert (4,2) {(4,4),(5,1),(5,3),(6,2)} := by decide
  rw [heq, show 2 = 1+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE
  rcases Finset.mem_union.mp hE with h | h
  · exact head5_11 E h
  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact pair5_10 T hT
end F840
