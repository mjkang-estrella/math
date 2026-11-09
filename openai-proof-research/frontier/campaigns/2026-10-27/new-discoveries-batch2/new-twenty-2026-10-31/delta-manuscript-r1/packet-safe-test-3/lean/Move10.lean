import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move10 : YYDelta g11 g10 := by
  unfold YYDelta
  dsimp only [g11, g10]
  refine ⟨12, 3, 7, 10, (fun i => (⟨if i.val < 12 then i.val else i.val + 1, by split <;> omega⟩ : Fin 13)), ?_⟩
  decide
end Concrete
