import MeanAlgebra

open Real Set
namespace ClassicalMeanRange

/-- The elementary two-coordinate convexity comparison at equal sums. -/
lemma two_point_convex {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {a b c d : ℝ} (hc : c ∈ s) (hd : d ∈ s)
    (hdb : d ≤ b) (hba : b ≤ a) (hac : a ≤ c) (hab : a + b = c + d) :
    f a + f b ≤ f c + f d := by
  by_cases hac' : a = c
  · have hbd : b = d := by linarith
    simp [hac', hbd]
  have haclt : a < c := lt_of_le_of_ne hac hac'
  have hda : d < a := by
    by_contra h
    have h' : a ≤ d := le_of_not_gt h
    linarith
  have hdb' : d < b := by linarith
  have hbc : b < c := hba.trans_lt haclt
  have hcd : 0 < c - d := by linarith
  have h1 := hf.secant_mono_aux1 hd hc hda haclt
  have h2 := hf.secant_mono_aux1 hd hc hdb' hbc
  have heq : (c - a) * f d + (a - d) * f c +
      ((c - b) * f d + (b - d) * f c) = (c - d) * (f c + f d) := by
    calc
      _ = (c + c - (a + b)) * f d + ((a + b) - d - d) * f c := by ring
      _ = _ := by rw [hab]; ring
  have hs : (c - d) * (f a + f b) ≤ (c - d) * (f c + f d) := by
    rw [← heq, mul_add]
    exact add_le_add h1 h2
  exact (mul_le_mul_iff_right₀ hcd).mp hs

/-- Increasing convex functions preserve weak majorization of two coordinates. -/
lemma two_point_convex_mono {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    (hmono : MonotoneOn f s) {a b c d : ℝ} (hc : c ∈ s) (hd : d ∈ s)
    (hdb : d ≤ b) (hba : b ≤ a) (_hac : a ≤ c) (hab : a + b ≤ c + d) :
    f a + f b ≤ f c + f d := by
  let c' := a + b - d
  have hdc' : d ≤ c' := by dsimp [c']; linarith
  have hc'c : c' ≤ c := by dsimp [c']; linarith
  have hc' : c' ∈ s := hf.1.ordConnected.out hd hc ⟨hdc', hc'c⟩
  have ha : a ≤ c' := by dsimp [c']; linarith
  have heq : a + b = c' + d := by dsimp [c']; ring
  exact (two_point_convex hf hc' hd hdb hba ha heq).trans
    (add_le_add (hmono hc' hc hc'c) le_rfl)

lemma source_inequality_ge_one {n x y : ℝ} (hn : 1 ≤ n) (hx : 0 < x) (hy : 0 < y) :
    (arithmetic x y) ^ n + (geometric x y) ^ n ≤
      (quadratic x y) ^ n + (harmonic x y) ^ n := by
  have hp := means_pos hx hy
  have ho := means_order hx hy
  apply two_point_convex_mono (convexOn_rpow hn)
    (fun _ ha _ _ hab => Real.rpow_le_rpow ha hab (by linarith))
    hp.2.2.2.le hp.2.2.1.le ho.1 ho.2.1 ho.2.2
  exact means_sum hx hy

lemma source_inequality_nonpos {n x y : ℝ} (hn : n ≤ 0) (hx : 0 < x) (hy : 0 < y) :
    (arithmetic x y) ^ n + (geometric x y) ^ n ≤
      (quadratic x y) ^ n + (harmonic x y) ^ n := by
  have hp := means_pos hx hy
  have ho := means_order hx hy
  have hhg : Real.log (harmonic x y) ≤ Real.log (geometric x y) :=
    Real.log_le_log hp.2.2.1 ho.1
  have hga : Real.log (geometric x y) ≤ Real.log (arithmetic x y) :=
    Real.log_le_log hp.2.1 ho.2.1
  have haq : Real.log (arithmetic x y) ≤ Real.log (quadratic x y) :=
    Real.log_le_log hp.1 ho.2.2
  have hprod : Real.log (quadratic x y) + Real.log (harmonic x y) ≤
      Real.log (arithmetic x y) + Real.log (geometric x y) := by
    rw [← Real.log_mul hp.2.2.2.ne' hp.2.2.1.ne',
      ← Real.log_mul hp.1.ne' hp.2.1.ne']
    exact Real.log_le_log (mul_pos hp.2.2.2 hp.2.2.1) (means_product hx hy)
  have hh : Real.exp (n * Real.log (geometric x y)) +
      Real.exp (n * Real.log (arithmetic x y)) ≤
      Real.exp (n * Real.log (harmonic x y)) +
      Real.exp (n * Real.log (quadratic x y)) := by
    apply two_point_convex_mono convexOn_exp (fun _ _ _ _ h => Real.exp_le_exp.mpr h)
      (Set.mem_univ _) (Set.mem_univ _)
      (mul_le_mul_of_nonpos_left haq hn)
      (mul_le_mul_of_nonpos_left hga hn)
      (mul_le_mul_of_nonpos_left hhg hn)
    have h := mul_le_mul_of_nonpos_left hprod hn
    linarith
  simp only [Real.rpow_def_of_pos hp.1, Real.rpow_def_of_pos hp.2.1,
    Real.rpow_def_of_pos hp.2.2.2, Real.rpow_def_of_pos hp.2.2.1]
  simpa only [mul_comm, add_comm] using hh

end ClassicalMeanRange
