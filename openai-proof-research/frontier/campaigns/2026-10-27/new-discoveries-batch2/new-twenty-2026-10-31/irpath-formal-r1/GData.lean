import General
open Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace IR350452
/-! ### The 9-vertex counterexample

`G9` is the complete tripartite graph `K_{3,3,3}` on the parts `{0,1,2}`, `{3,4,5}`, `{6,7,8}`
with the seven edges `05, 08, 14, 23, 26, 37, 56` deleted (20 edges). -/

/-- Edge list of `G9` (each edge once, smaller endpoint first). -/
def edges9 : List (ℕ × ℕ) :=
  [(0,3),(0,4),(0,6),(0,7),(1,3),(1,5),(1,6),(1,7),(1,8),(2,4),
   (2,5),(2,7),(2,8),(3,6),(3,8),(4,6),(4,7),(4,8),(5,7),(5,8)]

def adj9 (a b : Fin 9) : Bool :=
  decide ((a.val, b.val) ∈ edges9) || decide ((b.val, a.val) ∈ edges9)

def G9 : SimpleGraph (Fin 9) where
  Adj a b := adj9 a b = true
  symm := by
    constructor
    intro a b h
    revert a b
    decide
  loopless := by
    constructor
    intro a
    revert a
    decide

instance : DecidableRel G9.Adj := fun a b => inferInstanceAs (Decidable (adj9 a b = true))

instance (D : Finset (Fin 9)) : Decidable (Irredundant G9 D) := by
  unfold Irredundant IsPrivateNbr; infer_instance

instance (A B : Finset (Fin 9)) : Decidable (Swap G9 A B) := by
  unfold Swap; infer_instance

/-- The nine IR-sets, listed in path order. -/
def walk : Fin 9 → Finset (Fin 9)
  | 0 => {0, 1, 2} | 1 => {0, 2, 7} | 2 => {0, 4, 7} | 3 => {4, 6, 7} | 4 => {6, 7, 8}
  | 5 => {1, 6, 8} | 6 => {1, 3, 8} | 7 => {3, 5, 8} | 8 => {3, 4, 5}

end IR350452
