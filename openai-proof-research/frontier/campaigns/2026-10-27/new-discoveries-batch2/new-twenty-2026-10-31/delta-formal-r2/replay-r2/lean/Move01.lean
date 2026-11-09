import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move1 : YYDelta g1 g2 := by
  unfold YYDelta
  dsimp only [g1, g2]
  refine ⟨0, 1, 8, 15, (fun i => (⟨if i.val < 0 then i.val else i.val + 1, by split <;> omega⟩ : Fin 17)), ?_⟩
  decide
end Concrete
