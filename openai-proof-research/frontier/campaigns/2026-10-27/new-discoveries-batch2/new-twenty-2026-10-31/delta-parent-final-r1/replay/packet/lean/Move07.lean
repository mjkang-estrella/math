import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move7 : YYDelta g8 g7 := by
  unfold YYDelta
  dsimp only [g8, g7]
  refine ⟨11, 1, 6, 8, (fun i => (⟨if i.val < 11 then i.val else i.val + 1, by split <;> omega⟩ : Fin 12)), ?_⟩
  decide
end Concrete
