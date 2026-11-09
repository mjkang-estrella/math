import UlasFinal3
open Ulas.Round3 Polynomial
-- A uniform gain of two would fail on input y.
example : Weighted 2 (reduced 0 (monomial 1 2)) := by
  exact weighted_reduced 0 0 (monomial 1 2) (by
    exact weighted_monomial 0 1 2 (by norm_num))
