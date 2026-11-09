import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move5 : YYDelta g5 g6 := by
  unfold YYDelta
  dsimp only [g5, g6]
  refine ⟨7, 2, 5, 10, (fun i => (⟨if i.val < 7 then i.val else i.val + 1, by split <;> omega⟩ : Fin 13)), ?_⟩
  decide
end Concrete
