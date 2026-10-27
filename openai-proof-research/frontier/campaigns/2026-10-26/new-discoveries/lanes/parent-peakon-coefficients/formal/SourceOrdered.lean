import SourceHyperbolic
import CoefficientFamilies

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace PeakonCoefficients

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

def sourceLax (r : n → ℂ) (q : n → ℝ) (nu lam xi : ℂ) : Matrix n n ℂ :=
  sourceS r q nu + lam • sourceT r q nu + xi • sourceA r q nu

def sourceHamiltonian (r : n → ℂ) (q : n → ℝ) (nu gamma : ℂ) (k : ℕ) : ℂ :=
  (k : ℂ) * Matrix.trace ((sourceT r q nu + (gamma / 2) • sourceA r q nu) *
    (sourceS r q nu + sourceA r q nu) ^ (k - 1))

omit [Fintype n] [DecidableEq n] in
theorem sourceLax_ordered (r : n → ℂ) (q : n → ℝ) (nu lam xi : ℂ) (hq : Antitone q) :
    sourceLax r q nu lam xi = algebraicLax (sourceU r q nu) (sourceV r q nu) lam xi := by
  rw [algebraicLax, ← sourceS_add_A_ordered r q nu hq, ← sourceA_eq_skew,
    ← sourceT_eq_symmetric, add_sub_cancel_right]
  rfl

theorem sourceHamiltonian_ordered (r : n → ℂ) (q : n → ℝ) (nu gamma : ℂ)
    (hq : Antitone q) (k : ℕ) :
    sourceHamiltonian r q nu gamma k = rawHamiltonian (sourceU r q nu) (sourceV r q nu) gamma k := by
  unfold sourceHamiltonian rawHamiltonian hamiltonianDirection
  rw [sourceS_add_A_ordered r q nu hq, sourceA_eq_skew, sourceT_eq_symmetric]

theorem source_trace_partition_ordered (r : n → ℂ) (q : n → ℝ) (nu lam xi gamma : ℂ)
    (hq : Antitone q) (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) (m : ℕ) (hm : 0 < m) :
    Matrix.trace (sourceLax r q nu lam xi ^ m) =
      ∑ j ∈ Finset.range m, ∑ p ∈ (Finset.Icc 1 (Fintype.card n)).sym (j + 1),
        if p.val.sum = m then coefficientWeight (K := ℂ) m p.val * lam ^ (j + 1) *
          (p.val.map (sourceHamiltonian r q nu gamma)).prod else 0 := by
  rw [sourceLax_ordered r q nu lam xi hq]
  simpa only [sourceHamiltonian_ordered r q nu gamma hq] using
    trace_partition_weights (sourceU r q nu) (sourceV r q nu) lam xi gamma hcurve m hm

end PeakonCoefficients
