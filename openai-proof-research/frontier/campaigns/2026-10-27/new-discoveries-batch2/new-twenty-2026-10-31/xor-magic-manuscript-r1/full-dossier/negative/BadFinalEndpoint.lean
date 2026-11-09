import FinalExistence
example : XorMagic.ClosedExists 4 12 := by
  exact XorMagic.corrected_all 4 (by decide) |>.2 12 (by decide) (by decide) (by decide)
