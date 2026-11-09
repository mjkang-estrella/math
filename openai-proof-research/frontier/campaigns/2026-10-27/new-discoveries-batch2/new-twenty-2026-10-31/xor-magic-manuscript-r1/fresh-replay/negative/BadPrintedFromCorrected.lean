import FinalExistence
example : XorMagic.PrintedAt 4 := by
  obtain ⟨ho,hc⟩ := XorMagic.corrected_all 4 (by decide)
  constructor
  · exact ho
  · intro d hd hl hu
    apply hc d hd hl
    omega
