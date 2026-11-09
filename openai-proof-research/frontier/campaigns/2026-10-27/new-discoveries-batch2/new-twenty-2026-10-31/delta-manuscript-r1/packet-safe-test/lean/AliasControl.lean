import Controls
namespace AliasControl
open Literal
def rows : Delta153.Graph :=
 [[0,1,0,1,0,2,2,0,0],[1,0,1,3,1,0,0,0,0],[0,1,0,0,1,0,0,2,2],
  [1,3,0,0,0,0,0,0,0],[0,1,1,0,0,0,0,0,0],[2,0,0,0,0,0,0,0,0],
  [2,0,0,0,0,0,0,0,0],[0,0,2,0,0,0,0,0,0],[0,0,2,0,0,0,0,0,0]]
def graph : Graph where
  order := 9
  edge i j := Delta153.edge rows i.val j.val
  symm := by decide
  loopless := by decide

def chain : Chain graph 1 where
  base i := ⟨i.val, by have := i.isLt; change i.val < 9; omega⟩
  apex i := ⟨3 + i.val, by have := i.isLt; change 3 + i.val < 9; omega⟩
  left i := ⟨5 + i.val, by have := i.isLt; change 5 + i.val < 9; omega⟩
  right i := ⟨7 + i.val, by have := i.isLt; change 7 + i.val < 9; omega⟩
  attach _ := ⟨3, by decide⟩
  base_injective := by decide
  base_degree := by decide
  left_end := by unfold EndVertex; decide
  right_end := by unfold EndVertex; decide
  capacity := by decide

theorem contains_chain : HasChain graph := ⟨1, ⟨chain⟩⟩
theorem internal_triple : graph.edge ⟨1, by decide⟩ ⟨3, by decide⟩ = 3 := by decide
#print axioms contains_chain
end AliasControl
