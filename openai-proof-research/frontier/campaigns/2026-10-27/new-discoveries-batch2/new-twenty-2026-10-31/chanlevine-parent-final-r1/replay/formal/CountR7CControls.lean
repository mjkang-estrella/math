import CountR6Controls
import CountR7CFinal
namespace ChanLevine.Round7C.Controls
open Round6

def mixedRotor (v : ZMod 3) : Bool := v == 0

theorem mixed_has_facing : mixedRotor 0 = true ∧ mixedRotor (0+1) = false := by decide

theorem constant_has_no_facing :
    ∀ v : ZMod 3, ¬ ((fun _ => true) v = true ∧ (fun _ => true) (v+1) = false) := by decide

theorem zero_value : Round7C.matchingSeries (n := 3) (1 : ℚ) 0 = 2 := by
  rw [Round7C.matchingSeries_zero]
  norm_num

theorem target_type : MatchingCountConvolution := Round7C.matchingCountConvolution
end ChanLevine.Round7C.Controls
