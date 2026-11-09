import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

theorem probe_algebra (z : ℂ) (p : Polynomial ℝ) (I : Ideal ℝ)
    (q : ℝ ⧸ I) :
    z + 0 = z ∧ p + 0 = p ∧ q + 0 = q ∧ (2 : ℝ) + 3 = 5 := by
  constructor
  · exact add_zero z
  constructor
  · exact add_zero p
  constructor
  · exact add_zero q
  · norm_num
