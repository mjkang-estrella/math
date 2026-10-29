import C10_2_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace C10_2_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def edges : List (Fin 16 × Fin 16) := [(0,1),(0,2),(1,0),(1,3),(2,0),(2,3),(3,1),(3,2),(3,4),(3,5),(4,3),(4,6),(5,3),(5,6),(6,4),(6,5),(6,7),(6,8),(7,6),(7,9),(8,6),(8,9),(9,7),(9,8),(9,10),(9,11),(10,9),(10,12),(11,9),(11,12),(12,10),(12,11),(12,13),(12,14),(13,12),(13,15),(14,12),(14,15),(15,13),(15,14)]
theorem edge_mem : ∀ v w : Fin 16, Adj (point v) (point w) → (v,w) ∈ edges := by decide
end C10_2_1
