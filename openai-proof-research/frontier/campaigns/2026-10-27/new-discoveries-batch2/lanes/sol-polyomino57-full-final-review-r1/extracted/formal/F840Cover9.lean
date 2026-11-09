import F840Cover10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem head9 : ∀ E ∈ ({(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 2, insert (4,0) E ∈ pairs.map Prod.fst := by decide
theorem cover9 : ∀ E ∈ ({(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 3, E ∈ pairs.map Prod.fst := by
  intro E hE
  have heq : ({(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint) = insert (4,0) {(4,2),(4,4),(5,1),(5,3),(6,2)} := by decide
  rw [heq, show 3 = 2+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE
  rcases Finset.mem_union.mp hE with h | h
  · exact cover10 E h
  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact head9 T hT
end F840
