import UlasInitialization
import Mathlib.Algebra.Polynomial.Div
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem parityPair_zero (E : ℕ) : (parityPair E).1.eval 0 = if E = 0 then 1 else 0 := by
  cases E with
  | zero => simp [parityPair]
  | succ E => simp [parityPair]

theorem parityPair_neg_one (E : ℕ) : (parityPair E).1.eval (-1) = (-1:ℤ)^E := by
  induction E with
  | zero => simp [parityPair]
  | succ E ih => simp [parityPair, ih, pow_succ]

theorem polyEven_eval_zero (F : Polynomial ℤ) : (polyEven F).eval 0 = F.eval 0 := by
  classical
  simp only [polyEven, eval_finsetSum, eval_mul, eval_C, parityPair_zero]
  simp only [← Polynomial.coeff_zero_eq_eval_zero]
  simp
  intro h; exact h.symm

theorem polyEven_eval_neg_one (F : Polynomial ℤ) : (polyEven F).eval (-1) = F.eval (-1) := by
  classical
  simp only [polyEven, eval_finsetSum, eval_mul, eval_C, parityPair_neg_one]
  exact (Polynomial.eval_eq_sum).symm

theorem polyTransfer_eval_zero (m : ℕ) (F : Polynomial ℤ) :
    (polyTransfer m F).eval 0 = F.eval 0 := by
  simp [polyTransfer, polyEven_eval_zero]

theorem polyTransfer_eval_neg_one (m : ℕ) (F : Polynomial ℤ) :
    (polyTransfer m F).eval (-1) = (-1:ℤ)^m * F.eval (-1) := by
  simp [polyTransfer, polyEven_eval_neg_one]

theorem polyIter_eval_zero (m j : ℕ) : (polyIter m j).eval 0 = 1 := by
  induction j with
  | zero => simp [polyIter]
  | succ j ih => simpa [polyIter, polyTransfer_eval_zero] using ih

theorem polyIter_eval_neg_one (m j : ℕ) :
    (polyIter m j).eval (-1) = ((-1:ℤ)^m)^j := by
  induction j with
  | zero => simp [polyIter]
  | succ j ih => simp [polyIter, polyTransfer_eval_neg_one, ih, pow_succ, mul_comm]

/-- Genuine integral initial representative, linked to the frozen universal polynomial.
This existence lemma alone asserts no coefficient estimates. -/
theorem initial_representative (m : ℕ) : ∃ R : Polynomial ℤ,
    polyIter m 2 - 1 = Polynomial.X*(1+Polynomial.X)*R ∧
    Round2.transferDiff m 0 = y*(1+y)*ev R := by
  let F := polyIter m 2 - 1
  have hz : F.eval 0 = 0 := by simp [F, polyIter_eval_zero]
  have hn : F.eval (-1) = 0 := by
    simp only [F, eval_sub, eval_one, polyIter_eval_neg_one]
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
    norm_num
  have hx : Polynomial.X ∣ F := by
    rw [Polynomial.X_dvd_iff]; simpa [← Polynomial.coeff_zero_eq_eval_zero] using hz
  obtain ⟨Q,hQ⟩ := hx
  have hqn : Q.eval (-1) = 0 := by
    rw [hQ] at hn
    simpa using hn
  have hq : Polynomial.X - Polynomial.C (-1:ℤ) ∣ Q :=
    (dvd_iff_isRoot).mpr hqn
  obtain ⟨R,hR⟩ := hq
  have hf : F = Polynomial.X*(1+Polynomial.X)*R := by
    rw [hQ,hR]; simp; ring
  refine ⟨R,hf,?_⟩
  rw [transferDiff_polynomial]
  change ev F = _
  rw [hf]
  simp

theorem initial_constant (m : ℕ) : ∃ R : Polynomial ℤ,
    Round2.transferDiff m 0 = y*(1+y)*ev R ∧
    3*R.coeff 0 = 2*(m:ℤ)^2*((m:ℤ)+1)*((m:ℤ)+5) := by
  obtain ⟨R,_,hR⟩ := initial_representative m
  exact ⟨R,hR,initial_constant_polynomial m R hR⟩
end Ulas.Round5Odd
