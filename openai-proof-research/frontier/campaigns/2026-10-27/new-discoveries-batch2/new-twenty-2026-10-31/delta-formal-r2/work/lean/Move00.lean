import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move0 : YYDelta g0 g1 := by
  unfold YYDelta
  dsimp only [g0, g1]
  refine ⟨0, 3, 6, 14, (fun i => (⟨if i.val < 0 then i.val else i.val + 1, by split <;> omega⟩ : Fin 18)), ?_⟩
  decide
end Concrete
