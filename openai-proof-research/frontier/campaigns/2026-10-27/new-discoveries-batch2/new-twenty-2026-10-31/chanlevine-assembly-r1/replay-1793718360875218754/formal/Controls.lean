import Endpoint
open scoped BigOperators
namespace ChanLevine.Controls
def start : SignedConfig 3 := ⟨fun k => if k = 0 then 1 else 0, fun _ => true⟩
theorem flips_before_move : target start 0 = 2 := by decide
theorem sends_left : (fire start 0).x 2 = 1 := by decide
theorem flips_at_source : (fire start 0).q 0 = false := by decide
theorem legal_example : Step start (fire start 0) := ⟨0, by decide, rfl⟩
def wrongWeight (c : SignedConfig 3) : ZMod 3 :=
  (∑ k, k * (c.x k : ZMod 3)) + ∑ k, if c.q k then 1 else 0
theorem wrong_weight_rejected : wrongWeight start ≠ wrongWeight (fire start 0) := by decide
theorem empty_recurrence_rejected : ¬ Recurrent (SignedConfig.mk (fun _ : ZMod 3 => 0) (fun _ => true)) :=
  zero_not_recurrent _
end ChanLevine.Controls
