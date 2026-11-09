import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def edges : List (Fin 24 × Fin 24) := [(0,3),(0,4),(1,4),(1,5),(2,5),(2,6),(3,0),(3,7),(4,0),(4,1),(4,7),(4,8),(5,1),(5,2),(5,8),(5,9),(6,2),(6,9),(7,3),(7,4),(7,10),(7,11),(8,4),(8,5),(8,11),(8,12),(9,5),(9,6),(9,12),(9,13),(10,7),(10,14),(11,7),(11,8),(11,14),(11,15),(12,8),(12,9),(12,15),(12,16),(13,9),(13,16),(14,10),(14,11),(14,17),(14,18),(15,11),(15,12),(15,18),(15,19),(16,12),(16,13),(16,19),(16,20),(17,14),(17,21),(18,14),(18,15),(18,21),(18,22),(19,15),(19,16),(19,22),(19,23),(20,16),(20,23),(21,17),(21,18),(22,18),(22,19),(23,19),(23,20)]
theorem edge_mem : ∀ v w : Fin 24, Adj (point v) (point w) → (v,w) ∈ edges := by decide
end R6_6_1
