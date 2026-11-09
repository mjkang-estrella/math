import F840Head1_2
import F840Cover2
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace F840
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof
theorem head1 : ∀ E ∈ ({(1,1),(2,-2),(2,0),(2,2),(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 2, insert (1,-1) E ∈ pairs.map Prod.fst := head1_2
theorem cover1 : ∀ E ∈ ({(1,-1),(1,1),(2,-2),(2,0),(2,2),(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint).powersetCard 3, E ∈ pairs.map Prod.fst := by
  intro E hE
  have heq : ({(1,-1),(1,1),(2,-2),(2,0),(2,2),(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} : Finset GridPoint) = insert (1,-1) {(1,1),(2,-2),(2,0),(2,2),(3,-1),(3,1),(3,3),(4,0),(4,2),(4,4),(5,1),(5,3),(6,2)} := by decide
  rw [heq, show 3 = 2+1 from rfl, Finset.powersetCard_succ_insert (by decide)] at hE
  rcases Finset.mem_union.mp hE with h | h
  · exact cover2 E h
  · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact head1 T hT
end F840
