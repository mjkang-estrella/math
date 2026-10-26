import AppellRoots

noncomputable section
open Finset Polynomial
namespace OddRootMeans

def meanPolynomial (a : ℕ → ℂ) (D : ℕ) : ℂ[X] :=
  ∑ j ∈ range (D+1), C ((D.choose j : ℂ) * a (D-j)) * normMoment a j

lemma meanPolynomial_degree (a : ℕ → ℂ) (D : ℕ) :
    (meanPolynomial a D).natDegree ≤ D-1 := by
  unfold meanPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans ((normMoment_degree a j).trans (by
    have := mem_range.mp hj
    omega))

lemma meanPolynomial_roots (a : ℕ → ℂ) (ha : a 0 = 1) (D m : ℕ) :
    (m:ℂ) * (meanPolynomial a D).eval (m : ℂ) =
      ((appell a m).roots.map (fun z => (appell a D).eval z)).sum := by
  rw [meanPolynomial, eval_finsetSum, mul_sum, appell_sum_eval]
  apply sum_congr rfl
  intro j _
  rw [eval_mul, eval_C, mul_left_comm, appell_roots_moment a ha m j]

lemma normMoment_zero_value (a : ℕ → ℂ) (ha : a 0 = 1) (i : ℕ) :
    (normMoment a i).eval 0 = (-1 : ℂ)^i * a i := by
  cases i with
  | zero => simp [normMoment, ha]
  | succ n => exact normMoment_eval_zero a n

lemma odd_sign_reflect (D j : ℕ) (hD : Odd D) (hj : j≤D) :
    (-1 : ℂ)^(D-j) = -(-1 : ℂ)^j := by
  have hprod : (-1 : ℂ)^(D-j) * (-1 : ℂ)^j = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, hD.neg_one_pow]
  have hsquare : ((-1 : ℂ)^j)^2 = 1 := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  linear_combination (-1 : ℂ)^j * hprod - (-1 : ℂ)^(D-j) * hsquare

lemma meanPolynomial_zero (a : ℕ → ℂ) (ha : a 0 = 1) (D : ℕ) (hD : Odd D) :
    (meanPolynomial a D).eval 0 = 0 := by
  simp only [meanPolynomial, eval_finsetSum, eval_mul, eval_C,
    normMoment_zero_value a ha]
  let f : ℕ → ℂ := fun j => (D.choose j : ℂ) * a (D-j) * ((-1 : ℂ)^j * a j)
  change ∑ j ∈ range (D+1), f j = 0
  have hreflect : (∑ j ∈ range (D+1), f j) =
      ∑ j ∈ range (D+1), f (D-j) := by
    simpa only [Nat.add_sub_cancel] using (sum_range_reflect f (D+1)).symm
  have hneg : (∑ j ∈ range (D+1), f (D-j)) =
      -(∑ j ∈ range (D+1), f j) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    have hj' : j≤D := by have := mem_range.mp hj; omega
    dsimp [f]
    rw [Nat.choose_symm hj', Nat.sub_sub_self hj', odd_sign_reflect D j hD hj']
    ring
  linear_combination (1/2 : ℂ)*hreflect + (1/2 : ℂ)*hneg

lemma meanPolynomial_at_degree (a : ℕ → ℂ) (ha : a 0 = 1) (D : ℕ) (hD : 0<D) :
    (meanPolynomial a D).eval (D : ℂ) = 0 := by
  have h := meanPolynomial_roots a ha D D
  have hz : ((appell a D).roots.map (fun z => (appell a D).eval z)).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro z hz
    rcases Multiset.mem_map.mp hz with ⟨r, hr, rfl⟩
    exact Polynomial.isRoot_of_mem_roots hr
  rw [hz] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr hD.ne')

end OddRootMeans
