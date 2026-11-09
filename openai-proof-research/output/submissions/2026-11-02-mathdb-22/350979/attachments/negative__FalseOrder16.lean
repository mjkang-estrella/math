import Control16
open ReviewerControl
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
-- A nonexistence control: this claims a triple has no valid containing path.
example : ∃ a b c : V16, a < b ∧ b < c ∧
    ∀ p ∈ witnesses, ¬ (valid p ∧ a ∈ p ∧ b ∈ p ∧ c ∈ p) := by
  decide
