import TabMinors
-- must FAIL: T₁ is not a 7-minor-level list of T₂'s chain
theorem neg2 : TabMinors.step TabMinors.B6 = TabMinors.A7 := by decide +kernel
