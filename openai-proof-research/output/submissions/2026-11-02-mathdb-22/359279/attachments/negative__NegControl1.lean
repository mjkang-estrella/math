import TabMinors
-- must FAIL: the two level-8 lists are permutations, not equal lists
theorem neg1 : TabMinors.A8 = TabMinors.B8 := by decide +kernel
