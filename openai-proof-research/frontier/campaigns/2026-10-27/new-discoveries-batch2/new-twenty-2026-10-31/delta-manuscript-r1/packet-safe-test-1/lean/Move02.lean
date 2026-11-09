import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move2 : YYDelta g2 g3 := by
  unfold YYDelta
  dsimp only [g2, g3]
  refine ⟨3, 0, 7, 11, (fun i => (⟨if i.val < 3 then i.val else i.val + 1, by split <;> omega⟩ : Fin 16)), ?_⟩
  decide
end Concrete
