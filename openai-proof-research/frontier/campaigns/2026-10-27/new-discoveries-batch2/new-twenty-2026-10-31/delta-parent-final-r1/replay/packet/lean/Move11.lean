import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move11 : YYDelta g11 g12 := by
  unfold YYDelta
  dsimp only [g11, g12]
  refine ⟨10, 1, 11, 12, (fun i => (⟨if i.val < 10 then i.val else i.val + 1, by split <;> omega⟩ : Fin 13)), ?_⟩
  decide
end Concrete
