/-! Negative control (expected to FAIL under -DwarningAsError=true): a `sorry` is rejected. -/

theorem neg_sorry : (2 : Nat) + 2 = 5 := by sorry
