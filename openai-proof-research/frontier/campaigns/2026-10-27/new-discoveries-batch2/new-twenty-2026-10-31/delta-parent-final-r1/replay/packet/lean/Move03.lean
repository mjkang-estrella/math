import Nodes
namespace Concrete
open Literal
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem move3 : YYDelta g3 g4 := by
  unfold YYDelta
  dsimp only [g3, g4]
  refine ⟨4, 1, 5, 8, (fun i => (⟨if i.val < 4 then i.val else i.val + 1, by split <;> omega⟩ : Fin 15)), ?_⟩
  decide
end Concrete
