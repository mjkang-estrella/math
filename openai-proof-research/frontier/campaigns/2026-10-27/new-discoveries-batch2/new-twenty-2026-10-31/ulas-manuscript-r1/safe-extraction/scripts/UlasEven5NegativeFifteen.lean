import UlasEven5Final
example (h : Ulas.FifteenBound) : ∃ n, 1 ≤ n ∧ Ulas.val 15 n = padicValNat 2 n + 6 :=
  Ulas.false_fifteen_control h
