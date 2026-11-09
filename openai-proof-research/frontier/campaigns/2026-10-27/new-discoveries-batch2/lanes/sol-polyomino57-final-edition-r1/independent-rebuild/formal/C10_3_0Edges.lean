import C10_3_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_3_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def edges : List (Fin 22 × Fin 22) := [(0,2),(1,2),(1,3),(2,0),(2,1),(2,4),(2,5),(3,1),(3,5),(4,2),(4,6),(5,2),(5,3),(5,6),(5,7),(6,4),(6,5),(6,8),(6,9),(7,5),(7,9),(8,6),(8,10),(9,6),(9,7),(9,10),(9,11),(10,8),(10,9),(10,12),(10,13),(11,9),(11,13),(12,10),(12,14),(13,10),(13,11),(13,14),(13,15),(14,12),(14,13),(14,16),(14,17),(15,13),(15,17),(16,14),(16,18),(17,14),(17,15),(17,18),(17,19),(18,16),(18,17),(18,20),(18,21),(19,17),(19,21),(20,18),(21,18),(21,19)]
theorem edge_mem : ∀ v w : Fin 22, Adj (point v) (point w) → (v,w) ∈ edges := by decide
end C10_3_0
