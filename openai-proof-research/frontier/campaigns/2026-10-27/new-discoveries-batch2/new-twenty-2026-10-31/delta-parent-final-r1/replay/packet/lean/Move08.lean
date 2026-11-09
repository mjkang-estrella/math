import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move8 : YYDelta g8 g9 := by
  unfold YYDelta
  dsimp only [g8, g9]
  refine ⟨6, 3, 4, 11, (fun i => (⟨if i.val < 6 then i.val else i.val + 1, by split <;> omega⟩ : Fin 12)), ?_⟩
  decide
end Concrete
