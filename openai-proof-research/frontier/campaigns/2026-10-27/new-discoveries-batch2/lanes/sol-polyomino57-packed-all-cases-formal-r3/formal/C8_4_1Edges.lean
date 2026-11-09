import C8_4_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C8_4_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def edges : List (Fin 22 × Fin 22) := [(0,2),(0,3),(1,3),(1,4),(2,0),(2,5),(3,0),(3,1),(3,5),(3,6),(4,1),(4,6),(5,2),(5,3),(5,7),(5,8),(6,3),(6,4),(6,8),(6,9),(7,5),(7,10),(8,5),(8,6),(8,10),(8,11),(9,6),(9,11),(10,7),(10,8),(10,12),(10,13),(11,8),(11,9),(11,13),(11,14),(12,10),(12,15),(13,10),(13,11),(13,15),(13,16),(14,11),(14,16),(15,12),(15,13),(15,17),(15,18),(16,13),(16,14),(16,18),(16,19),(17,15),(17,20),(18,15),(18,16),(18,20),(18,21),(19,16),(19,21),(20,17),(20,18),(21,18),(21,19)]
theorem edge_mem : ∀ v w : Fin 22, Adj (point v) (point w) → (v,w) ∈ edges := by decide
end C8_4_1
