import Mathlib
open PowerSeries Finset
open scoped PowerSeries
namespace TrigSource

noncomputable def geometric (D : ℕ) : PowerSeries ℝ := ∑ j∈Finset.range D, X^j

lemma geometric_mul (D : ℕ) : geometric D * (1-X) = 1-X^D := by
  induction D with
  | zero => simp [geometric]
  | succ D ih =>
    rw [geometric, Finset.sum_range_succ]
    change (geometric D + X^D)*(1-X)=1-X^(D+1)
    rw [add_mul, ih, pow_succ]
    ring

lemma geometric_constant (D : ℕ) (hD : 0<D) : constantCoeff (geometric D)=1 := by
  unfold geometric
  rw [map_sum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp [hD]

noncomputable def sourceRoot (D : ℕ) : PowerSeries ℝ :=
  (PowerSeries.binomialSeries ℝ (1/2:ℝ)).subst (geometric D-1)

lemma sourceRoot_square (D : ℕ) (hD : 0<D) : (sourceRoot D)^2=geometric D := by
  have hc : constantCoeff (geometric D-1)=0 := by simp [geometric_constant D hD]
  have hs : HasSubst (geometric D-1) := HasSubst.of_constantCoeff_zero' hc
  have hb : (PowerSeries.binomialSeries ℝ (1/2:ℝ))^2 = 1+X := by
    rw [pow_two, ← binomialSeries_add]
    norm_num
    simpa using (PowerSeries.binomialSeries_nat (R:=ℝ) (A:=ℝ) 1)
  unfold sourceRoot
  rw [← subst_pow hs, hb, subst_add hs, subst_X hs]
  have h1 : (1:PowerSeries ℝ).subst (geometric D-1)=1 := by
    simpa using (subst_C (a := geometric D-1) (1:ℝ))
  rw [h1]
  ring

lemma sourceRoot_constant (D : ℕ) (hD : 0<D) : constantCoeff (sourceRoot D)=1 := by
  unfold sourceRoot
  have hc : constantCoeff (geometric D-1)=0 := by simp [geometric_constant D hD]
  have h := constantCoeff_subst_of_constantCoeff_zero (R:=ℝ) (S:=ℝ) hc
    (PowerSeries.binomialSeries ℝ (1/2:ℝ))
  rw [constantCoeff_eq]
  simpa only [PowerSeries.binomialSeries_constantCoeff, map_one] using h

lemma sourceRoot_identity (D : ℕ) (hD : 0<D) :
    (sourceRoot D)^2*(1-X)=1-X^D := by
  rw [sourceRoot_square D hD, geometric_mul]

lemma root_ode (D : ℕ) (hD : 0 < D) (B : PowerSeries ℝ)
    (hroot : B^2*(1-X)=1-X^D) :
    2*(1-X)*(1-X^D)*derivative B =
      (1+((D:ℝ)-1) • (X^D) -(D:ℝ) • (X^(D-1)))*B := by
  have hd := congrArg (fun F : PowerSeries ℝ => derivative F) hroot
  simp only [Derivation.leibniz, map_sub, derivative_pow, derivative_one, derivative_X] at hd
  have hx : (X : PowerSeries ℝ)^(D-1)*X=X^D := by
    rw [← pow_succ]; congr 1; omega
  have hh : 2*(1-X)*B*derivative B = B^2-(D:PowerSeries ℝ)*(X^(D-1)) := by
    simp only [smul_eq_mul] at hd
    linear_combination hd
  have hQ : (1+((D:ℝ)-1) • (X^D) -(D:ℝ) • (X^(D-1)) : PowerSeries ℝ) =
      1-X^D-((D:PowerSeries ℝ)*(X^(D-1)))*(1-X) := by
    simp only [smul_eq_C_mul, map_sub, map_one, map_natCast]
    rw [← hx]
    ring
  rw [hQ]
  have hh' := congrArg (fun F : PowerSeries ℝ => F*B*(1-X)) hh
  linear_combination hh' + (B-2*(1-X)*derivative B)*hroot

end TrigSource
