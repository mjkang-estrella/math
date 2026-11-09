import F840Head4_6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem pair4_5 : ∀ T ∈ ({(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 1, insert (2,0) (insert (2,2) T) ∈ pairs.map Prod.fst := by decide
theorem head4_5 : ∀ E ∈ ({(2,2),(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 2, insert (2,0) E ∈ pairs.map Prod.fst := by
  intro E hE
  have heq : ({(2,2),(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint) = insert (2,2) {(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} := by decide
  rw [heq, show 2 = 1+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE
  rcases Finset.mem_union.mp hE with h | h
  · exact head4_6 E h
  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact pair4_5 T hT
end F840
