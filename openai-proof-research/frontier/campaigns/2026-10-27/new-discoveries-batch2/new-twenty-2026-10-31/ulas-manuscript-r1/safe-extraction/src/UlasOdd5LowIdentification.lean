import UlasOdd5PowerCoefficients
set_option linter.unusedSimpArgs false
open PowerSeries Polynomial
namespace Ulas.Round5Odd
open Round4

theorem ev_low (R : Polynomial ℤ) :
    coeff 0 (ev R) = R.coeff 0 ∧ coeff 1 (ev R) = R.coeff 1 ∧
    coeff 2 (ev R) = R.coeff 1+R.coeff 2 := by
  induction R using Polynomial.recOnHorner with
  | M0 => simp
  | MC R a h0 ha ih =>
    rcases ih with ⟨ih0,ih1,ih2⟩
    simp only [map_add,ev_C,Polynomial.coeff_add,ih0,ih1,ih2,
      PowerSeries.coeff_C,Polynomial.coeff_C]
    norm_num
  | MX R hR ih =>
    rcases ih with ⟨ih0,ih1,ih2⟩
    simp only [map_mul,ev_X]
    rw [y]
    norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      geomStep,ih0,ih1,ih2,Polynomial.coeff_mul_X,PowerSeries.coeff_X,Finset.filter_insert,Finset.filter_singleton]

theorem reduced_readout_low (m : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff m 0 = y*(1+y)*ev R) :
    diff m 2 = R.coeff 1+(2+coeff 1 (C^m))*R.coeff 0 ∧
    diff m 3 = R.coeff 2+(3+coeff 1 (C^m))*R.coeff 1+
      (3+2*coeff 1 (C^m)+coeff 2 (C^m))*R.coeff 0 := by
  have h2 := diff_reduced_readout m 0 2 R hR
  have h3 := diff_reduced_readout m 0 3 R hR
  simp only [pow_zero,one_mul,Round3.reducedIter] at h2 h3
  have hc : ∀ n, coeff n (C^m*(y*(1+y)*ev R)) =
      ∑ p ∈ Finset.antidiagonal n, coeff p.1 (C^m)*
        (∑ q ∈ Finset.antidiagonal p.2, (q.1:ℤ)*coeff q.2 (ev R)) := by
    intro n
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    rw [PowerSeries.coeff_mul]
    simp only [coeff_y_factor]
  rw [hc] at h2 h3
  obtain ⟨e0,e1,e2⟩ := ev_low R
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,e0,e1,e2] at h2 h3
  constructor
  · linear_combination h2
  · linear_combination h3
theorem initial_low1 (m : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff m 0 = y*(1+y)*ev R) :
    315*R.coeff 1 = lowNumerator1 (m:ℤ) := by
  have h0 := initial_constant_polynomial m R hR
  have hr := (reduced_readout_low m R hR).1
  have h1 := power_coeff_1 m
  norm_num at h1
  rw [h1] at hr
  unfold diff c at hr
  change coeff 8 (C^m)-coeff 2 (C^m) = _ at hr
  suffices he : 128*(315*R.coeff 1) = 128*lowNumerator1 (m:ℤ) by omega
  unfold lowNumerator1
  linear_combination power_coeff_8 m - 20160*(power_coeff_2 m) - 40320*hr -
    13440*(2+2*(m:ℤ))*h0

theorem initial_low2 (m : ℕ) (R : Polynomial ℤ)
    (hR : Round2.transferDiff m 0 = y*(1+y)*ev R) :
    467775*R.coeff 2 = lowNumerator2 (m:ℤ) := by
  have h0 := initial_constant_polynomial m R hR
  have hlow := initial_low1 m R hR
  have hr := (reduced_readout_low m R hR).2
  obtain ⟨_,h1,h2,_,_⟩ := q_pow_low m
  have h1' : coeff 1 (C^m) = 2*(m:ℤ) := by
    change c m 1 = _
    rw [c_low m 1 (by omega)]
    exact h1
  have h2' : coeff 2 (C^m) = 2*(m:ℤ)*((m:ℤ)+1) := by
    change c m 2 = _
    rw [c_low m 2 (by omega)]
    exact h2
  rw [h1',h2'] at hr
  change coeff 12 (C^m)-coeff 3 (C^m) = _ at hr
  suffices he : 1024*(467775*R.coeff 2) = 1024*lowNumerator2 (m:ℤ) by omega
  unfold lowNumerator1 at hlow
  unfold lowNumerator2
  linear_combination power_coeff_12 m - 79833600*(power_coeff_3 m) - 479001600*hr -
    1520640*(3+2*(m:ℤ))*hlow -
    159667200*(3+4*(m:ℤ)+2*(m:ℤ)*((m:ℤ)+1))*h0
end Ulas.Round5Odd
