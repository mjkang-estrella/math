import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move13 : YYDelta g13 g14 := by
  unfold YYDelta
  dsimp only [g13, g14]
  refine ⟨9, 1, 4, 10, (fun i => (⟨if i.val < 9 then i.val else i.val + 1, by split <;> omega⟩ : Fin 11)), ?_⟩
  decide
end Concrete
