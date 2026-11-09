import UlasOdd5Final
example : Ulas.diff 2 1 = 28 := by
  have h : Ulas.diff 2 1 = 56 := by
    unfold Ulas.diff
    rw [Ulas.c_low 2 4 (by omega), Ulas.c_low 2 1 (by omega), Ulas.q_2_4, Ulas.q_2_1]
    norm_num
  exact h
