import UlasEven5Final
example : ∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
    Ulas.val (2*k) n = padicValNat 2 n + 2*padicValNat 2 k + 2 := by
  intro k n hk hn
  exact (Ulas.Even5.evenFormula_proved k n hk hn).2
