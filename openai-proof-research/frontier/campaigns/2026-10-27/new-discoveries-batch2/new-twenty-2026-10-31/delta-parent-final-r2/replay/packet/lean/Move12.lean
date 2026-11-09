import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move12 : YYDelta g12 g13 := by
  unfold YYDelta
  dsimp only [g12, g13]
  refine ⟨7, 1, 10, 11, (fun i => (⟨if i.val < 7 then i.val else i.val + 1, by split <;> omega⟩ : Fin 12)), ?_⟩
  decide
end Concrete
