import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move6 : YYDelta g6 g7 := by
  unfold YYDelta
  dsimp only [g6, g7]
  refine ⟨11, 4, 7, 9, (fun i => (⟨if i.val < 11 then i.val else i.val + 1, by split <;> omega⟩ : Fin 12)), ?_⟩
  decide
end Concrete
