import Concrete
namespace Controls
open Literal
def rows : Delta153.Graph :=
  [[0,1,1,2,2,0,0],[1,0,1,0,0,2,2],[1,1,0,0,0,0,0],
   [2,0,0,0,0,0,0],[2,0,0,0,0,0,0],[0,2,0,0,0,0,0],[0,2,0,0,0,0,0]]
def control : Graph where
  order := 7
  edge i j := Delta153.edge rows i.val j.val
  symm := by decide
  loopless := by decide

def chain : Chain control 0 where
  base i := ⟨i.val, by have := i.isLt; change i.val < 7; omega⟩
  apex _ := ⟨2, by decide⟩
  left i := ⟨3 + i.val, by have := i.isLt; change 3 + i.val < 7; omega⟩
  right i := ⟨5 + i.val, by have := i.isLt; change 5 + i.val < 7; omega⟩
  attach := Fin.elim0
  base_injective := by decide
  base_degree := by decide
  left_end := by unfold EndVertex; decide
  right_end := by unfold EndVertex; decide
  capacity := by decide

theorem chain_positive : HasChain control := ⟨0, ⟨chain⟩⟩
theorem move_positive : ∃ g h, YYDelta g h := ⟨Concrete.g0, Concrete.g1, Concrete.move0⟩
#print axioms chain_positive
#print axioms move_positive
end Controls
