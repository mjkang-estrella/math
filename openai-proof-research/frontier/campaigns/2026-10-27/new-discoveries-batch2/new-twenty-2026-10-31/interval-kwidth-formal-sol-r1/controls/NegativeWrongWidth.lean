import IntervalControls
example (k n : Nat) : IntervalWidth.width k (fun _ : Fin n => (⟨0,1⟩ : IntervalWidth.Interval Nat)) = n+1 := IntervalWidth.overlapping_width k n
