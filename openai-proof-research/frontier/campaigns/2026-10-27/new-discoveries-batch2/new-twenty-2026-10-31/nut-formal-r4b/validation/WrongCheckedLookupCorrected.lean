import CheckedGraphIso
example : (Nut8.checkedEquiv (n := 2) [0, 1] (by decide) ⟨0, by omega⟩).val = 1 := by
  simp [Nut8.checkedEquiv, Nut8.checkedVertex, Equiv.ofBijective]
