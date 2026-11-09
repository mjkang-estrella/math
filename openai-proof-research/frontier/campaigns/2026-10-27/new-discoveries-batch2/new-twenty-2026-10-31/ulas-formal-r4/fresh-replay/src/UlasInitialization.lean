import UlasInvariant
set_option linter.unusedSimpArgs false
open PowerSeries
namespace Ulas.Round4
noncomputable def polyIter (m : ℕ) : ℕ → Polynomial ℤ
  | 0 => 1
  | j+1 => polyTransfer m (polyIter m j)

theorem transferIter_polynomial (m j : ℕ) : transferIter m j = ev (polyIter m j) := by
  induction j with
  | zero => simp [transferIter, polyIter]
  | succ j ih =>
    simp only [transferIter, ih, polyIter, polyTransfer]
    have hh : w^m*ev (polyIter m j) = ev ((1+2*Polynomial.X)^m*polyIter m j) := by
      simp only [map_mul, map_pow, map_add, map_one, map_ofNat, ev_X, w_y]
    rw [hh, sectionEven_ev]

theorem transferDiff_polynomial (m j : ℕ) :
    Round2.transferDiff m j = ev (polyIter m (j+2)-polyIter m j) := by
  simp [Round2.transferDiff, transferIter_polynomial]

@[simp] theorem ev_constant (R : Polynomial ℤ) : constantCoeff (ev R) = R.coeff 0 := by
  rw [ev_eq_sum, map_sum]
  simp [y, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_eq_sum, Polynomial.sum]

theorem initial_constant (m : ℕ) (R : Polynomial ℤ)
    (h0 : Round2.transferDiff m 0 = y*(1+y)*ev R) : R.coeff 0 = diff m 1 := by
  have hh := diff_reduced_readout m 0 1 R h0
  simp only [pow_zero, one_mul, Round3.reducedIter] at hh
  rw [← mul_assoc] at hh
  have hz : coeff 0 (C^m*(y*(1+y))) = 0 := by simp [y]
  have hone : coeff 1 (C^m*(y*(1+y))) = 1 := by
    rw [coeff_mul]
    simp [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, coeff_y_factor]
  rw [coeff_mul] at hh
  simpa [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, hz, hone,
    coeff_zero_eq_constantCoeff] using hh.symm

/-- The universal initial constant is now linked to any genuine reduced representative. -/
theorem initial_constant_polynomial (m : ℕ) (R : Polynomial ℤ)
    (h0 : Round2.transferDiff m 0 = y*(1+y)*ev R) :
    3*R.coeff 0 = 2*(m:ℤ)^2*((m:ℤ)+1)*((m:ℤ)+5) := by
  rw [initial_constant m R h0]
  exact diff_one_polynomial m
end Ulas.Round4
