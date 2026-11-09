import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move9 : YYDelta g10 g9 := by
  unfold YYDelta
  dsimp only [g10, g9]
  refine ⟨11, 4, 7, 10, (fun i => (⟨if i.val < 11 then i.val else i.val + 1, by split <;> omega⟩ : Fin 12)), ?_⟩
  decide
end Concrete
