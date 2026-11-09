import UlasBinomial
open PowerSeries
namespace Ulas.Round4
noncomputable def recursiveIter (m : ℕ) (R : Polynomial ℤ) : ℕ → Polynomial ℤ
  | 0 => R
  | j+1 => recursiveReduced m (recursiveIter m R j)

theorem transferDiff_reduced (m : ℕ) (R : Polynomial ℤ)
    (h0 : Round2.transferDiff m 0 = y*(1+y)*ev R) (j : ℕ) :
    Round2.transferDiff m j = y*(1+y)*ev (Round3.reducedIter m R j) := by
  induction j with
  | zero => exact h0
  | succ j ih => rw [Round2.transferDiff_succ, ih, lemma_R_unconditional]; rfl

theorem diff_reduced_readout (m j n : ℕ) (R : Polynomial ℤ)
    (h0 : Round2.transferDiff m 0 = y*(1+y)*ev R) :
    diff m (2^j*n) = coeff n (C^m*(y*(1+y)*ev (Round3.reducedIter m R j))) := by
  rw [Round2.diff_readout, transferDiff_reduced m R h0]

/-- Coefficient divisibility is stable under products of integer series. -/
theorem coeff_dvd_mul_right (d : ℤ) (f g : PowerSeries ℤ)
    (hg : ∀ n, d ∣ coeff n g) (n : ℕ) : d ∣ coeff n (f*g) := by
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro a _
  exact dvd_mul_of_dvd_right (hg a.2) _

theorem coeff_dvd_ev (d : ℤ) (R : Polynomial ℤ)
    (hR : ∀ E, d ∣ R.coeff E) (n : ℕ) : d ∣ coeff n (ev R) := by
  rw [ev_eq_sum, map_sum]
  apply Finset.dvd_sum
  intro E _
  simpa using dvd_mul_of_dvd_left (hR E) (coeff n (y^E))

/-- Lemma W now applies to the actual differences, conditional only on an explicit
initial representative; the operator bridge is no longer a premise. -/
theorem diff_dvd_of_weighted (m v j n : ℕ) (R : Polynomial ℤ)
    (h0 : Round2.transferDiff m 0 = y*(1+y)*ev R)
    (hw : Round3.Weighted v R) : (2:ℤ)^(v+j) ∣ diff m (2^j*n) := by
  rw [diff_reduced_readout m j n R h0]
  rw [← mul_assoc]
  apply coeff_dvd_mul_right
  apply coeff_dvd_ev
  exact Round3.weighted_coeff_dvd (Round3.weighted_reducedIter m v j R hw)

/-- Under the nonzero hypothesis required by padicValInt's zero convention. -/
theorem valuation_of_weighted (m v j n : ℕ) (R : Polynomial ℤ)
    (h0 : Round2.transferDiff m 0 = y*(1+y)*ev R)
    (hw : Round3.Weighted v R) (hnz : diff m (2^j*n) ≠ 0) :
    v+j ≤ val m (2^j*n) := by
  have hd := diff_dvd_of_weighted m v j n R h0 hw
  exact ((padicValInt_dvd_iff (v+j) _).mp hd).resolve_left hnz
end Ulas.Round4
