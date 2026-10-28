import ScalarCore

open scoped BigOperators
namespace FourProjection

lemma weighted_bound {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℝ) (b : J → ℝ) (w : I → J → ℝ)
    (hrow : ∀ i, ∑ j, w i j ≤ 1) (hcol : ∀ j, ∑ i, w i j ≤ 1) :
    ∑ i, ∑ j, (a i ^ 2 + b j ^ 2) * w i j ≤
      (∑ i, a i ^ 2) + ∑ j, b j ^ 2 := by
  have hfirst : ∑ i, ∑ j, a i ^ 2 * w i j =
      ∑ i, a i ^ 2 * ∑ j, w i j := by simp_rw [Finset.mul_sum]
  have hsecond : ∑ i, ∑ j, b j ^ 2 * w i j =
      ∑ j, b j ^ 2 * ∑ i, w i j := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  calc
    _ = (∑ i, a i ^ 2 * ∑ j, w i j) + ∑ j, b j ^ 2 * ∑ i, w i j := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [hfirst, hsecond]
    _ ≤ _ := add_le_add
      (Finset.sum_le_sum fun i _ => by simpa using mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (a i)))
      (Finset.sum_le_sum fun j _ => by simpa using mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg (b j)))

/-- Spectral finite-array core only. This theorem does NOT include the projection/frame bridge. -/
theorem spectral_core {I J : Type*} [Fintype I] [Fintype J]
    (a : I → ℝ) (b : J → ℝ) (k l : I → J → ℂ) (u v : I → J → ℝ)
    (ha : ∀ i, a i ^ 2 < 1) (hb : ∀ j, b j ^ 2 < 1)
    (hu0 : ∀ i j, 0 ≤ u i j) (hv0 : ∀ i j, 0 ≤ v i j)
    (hu : ∀ i j, u i j ^ 2 = (1+a i)*(1+b j))
    (hv : ∀ i j, v i j ^ 2 = (1-a i)*(1-b j))
    (hrel : ∀ i j, (u i j:ℂ)*k i j+(v i j:ℂ)*l i j=0)
    (hkrow : ∀ i, ∑ j, Complex.normSq (k i j) ≤ 1)
    (hkcol : ∀ j, ∑ i, Complex.normSq (k i j) ≤ 1)
    (hlrow : ∀ i, ∑ j, Complex.normSq (l i j) ≤ 1)
    (hlcol : ∀ j, ∑ i, Complex.normSq (l i j) ≤ 1) :
    (∑ i, ∑ j, Complex.normSq (k i j+l i j)) / 4 ≤
      ((∑ i, a i ^ 2) + ∑ j, b j ^ 2) / 2 := by
  have hp : ∑ i, ∑ j, Complex.normSq (k i j+l i j) ≤
      ∑ i, ∑ j, (a i^2+b j^2)*(Complex.normSq (k i j)+Complex.normSq (l i j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      complex_pair (a i) (b j) (u i j) (v i j) (k i j) (l i j)
        (ha i) (hb j) (hu0 i j) (hv0 i j) (hu i j) (hv i j) (hrel i j)
  have hk := weighted_bound a b (fun i j => Complex.normSq (k i j)) hkrow hkcol
  have hl := weighted_bound a b (fun i j => Complex.normSq (l i j)) hlrow hlcol
  simp_rw [mul_add, Finset.sum_add_distrib] at hp
  linarith

#print axioms weighted_bound
#print axioms spectral_core
end FourProjection
