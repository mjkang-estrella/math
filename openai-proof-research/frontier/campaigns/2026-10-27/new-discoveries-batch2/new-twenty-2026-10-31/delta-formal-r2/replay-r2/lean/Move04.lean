import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move4 : YYDelta g4 g5 := by
  unfold YYDelta
  dsimp only [g4, g5]
  refine ⟨6, 4, 7, 10, (fun i => (⟨if i.val < 6 then i.val else i.val + 1, by split <;> omega⟩ : Fin 14)), ?_⟩
  decide
end Concrete
