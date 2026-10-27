import CombinedError
import CotBoundary
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace EulerTuran
def bilateral (n : ℕ) : ℝ := ∑' m : ℤ, (1/(4*(m:ℝ)+1))^(n+1)
lemma arithmetic_reciprocal_summable (a b : ℝ) (ha : 0 < a) {p : ℕ} (hp : 1 < p) :
    Summable (fun k : ℕ => (1/(a*(k:ℝ)+b))^p) := by
  have hh := ((Real.summable_one_div_nat_add_rpow (b/a) (p:ℝ)).2
    (by exact_mod_cast hp)).mul_left (1/a^p)
  simp only [Real.rpow_natCast] at hh
  have hid (k : ℕ) : ‖(1/(a*(k:ℝ)+b))^p‖ =
      1/a^p * (1/|(k:ℝ)+b/a|^p) := by
    rw [norm_pow, Real.norm_eq_abs, abs_div, abs_one]
    rw [show a*(k:ℝ)+b = a*((k:ℝ)+b/a) by field_simp]
    rw [abs_mul, abs_of_pos ha]
    rw [div_pow, one_pow, mul_pow]
    ring
  apply summable_norm_iff.mp
  exact hh.congr fun k => (hid k).symm
lemma bilateral_summable {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℤ => (1/(4*(m:ℝ)+1))^(n+1)) := by
  have hh := (shifted_reciprocal_summable (a := (1/4:ℝ)) (by omega : 1 < n+1)).mul_left
    ((1/4:ℝ)^(n+1))
  apply summable_norm_iff.mp
  apply hh.congr
  intro m
  rw [norm_pow, Real.norm_eq_abs, abs_div, abs_one]
  have hid : |4*(m:ℝ)+1| = 4*|(m:ℝ)+1/4| := by
    rw [show 4*(m:ℝ)+1 = 4*((m:ℝ)+1/4) by ring, abs_mul]
    norm_num
  rw [hid]
  simp only [div_pow, one_pow, mul_pow]
  ring
lemma bilateral_pair {n : ℕ} (hn : 1 ≤ n) :
    bilateral n = 1 + ∑' k : ℕ,
      ((1/(4*(k:ℝ)+5))^(n+1) + (-1:ℝ)^(n+1)*(1/(4*(k:ℝ)+3))^(n+1)) := by
  let f : ℤ → ℝ := fun m => (1/(4*(m:ℝ)+1))^(n+1)
  have ep (k : ℕ) : f ((k:ℤ)+1) = (1/(4*(k:ℝ)+5))^(n+1) := by
    dsimp [f]
    push_cast
    congr 2
    ring
  have em (k : ℕ) : f (-((k:ℤ)+1)) =
      (-1:ℝ)^(n+1)*(1/(4*(k:ℝ)+3))^(n+1) := by
    dsimp [f]
    push_cast
    rw [show 4*(-((k:ℝ)+1))+1 = -(4*(k:ℝ)+3) by ring, div_neg, neg_pow]
  have hp := arithmetic_reciprocal_summable 4 5 (by norm_num) (by omega : 1 < n+1)
  have hm := (arithmetic_reciprocal_summable 4 3 (by norm_num)
    (by omega : 1 < n+1)).mul_left ((-1:ℝ)^(n+1))
  have hp' : Summable (fun k : ℕ => f ((k:ℤ)+1)) := hp.congr fun k => (ep k).symm
  have hm' : Summable (fun k : ℕ => f (-((k:ℤ)+1))) := hm.congr fun k => (em k).symm
  calc
    bilateral n = (∑' k : ℕ, f ((k:ℤ)+1)) + f 0 +
        ∑' k : ℕ, f (-((k:ℤ)+1)) := tsum_of_add_one_of_neg_add_one hp' hm'
    _ = (∑' k : ℕ, (1/(4*(k:ℝ)+5))^(n+1)) + 1 +
        ∑' k : ℕ, (-1:ℝ)^(n+1)*(1/(4*(k:ℝ)+3))^(n+1) := by
      simp only [ep, em]
      norm_num [f]
    _ = _ := by rw [hp.tsum_add hm]; ring
lemma tsum_even_odd (f : ℕ → ℝ)
    (h0 : Summable (fun k => f (2*k))) (h1 : Summable (fun k => f (2*k+1))) :
    ∑' k, f k = (∑' k, f (2*k)) + ∑' k, f (2*k+1) := by
  rw [← Equiv.natSumNatEquivNat.tsum_eq f]
  have h0' : Summable ((f ∘ Equiv.natSumNatEquivNat) ∘ Sum.inl) := by
    simpa only [Function.comp_def, Equiv.natSumNatEquivNat_apply, Sum.elim_inl] using h0
  have h1' : Summable ((f ∘ Equiv.natSumNatEquivNat) ∘ Sum.inr) := by
    simpa only [Function.comp_def, Equiv.natSumNatEquivNat_apply, Sum.elim_inr] using h1
  simpa only [Function.comp_def, Equiv.natSumNatEquivNat_apply, Sum.elim_inl, Sum.elim_inr]
    using h0'.tsum_sum h1'
lemma positiveError_pair (n : ℕ) :
    positiveError n = ∑' k : ℕ,
      ((1/(4*(k:ℝ)+5))^(n+2) + (1/(4*(k:ℝ)+3))^(n+2)) := by
  have h3 := arithmetic_reciprocal_summable 4 3 (by norm_num) (by omega : 1 < n+2)
  have h5 := arithmetic_reciprocal_summable 4 5 (by norm_num) (by omega : 1 < n+2)
  have e0 (k : ℕ) : positiveTerm n (2*k) = (1/(4*(k:ℝ)+3))^(n+2) := by
    dsimp [positiveTerm]
    push_cast
    congr 2
    ring
  have e1 (k : ℕ) : positiveTerm n (2*k+1) = (1/(4*(k:ℝ)+5))^(n+2) := by
    dsimp [positiveTerm]
    push_cast
    congr 2
    ring
  rw [positiveError, tsum_even_odd (positiveTerm n)
    (h3.congr fun k => (e0 k).symm) (h5.congr fun k => (e1 k).symm)]
  simp only [e0, e1]
  rw [h5.tsum_add h3]
  ring
lemma bilateral_even {n : ℕ} (hn : 1 ≤ n) (he : Even n) :
    bilateral n = 1-evenError n := by
  have hs : (-1:ℝ)^(n+1) = -1 := by rw [pow_add, he.neg_one_pow]; norm_num
  rw [bilateral_pair hn]
  simp only [hs, neg_one_mul]
  have hh : (fun k : ℕ => (1/(4*(k:ℝ)+5))^(n+1) - (1/(4*(k:ℝ)+3))^(n+1)) =
      fun k => -evenTerm n k := by ext k; dsimp [evenTerm]; ring
  simp only [← sub_eq_add_neg, hh, tsum_neg, evenError]
lemma bilateral_odd {n : ℕ} (hn : 1 ≤ n) (ho : Odd n) :
    bilateral n = 1+positiveError (n-1) := by
  have hs : (-1:ℝ)^(n+1) = 1 := by rw [pow_add, ho.neg_one_pow]; norm_num
  rw [bilateral_pair hn, positiveError_pair]
  simp only [hs, one_mul, show n-1+2 = n+1 by omega]
end EulerTuran
