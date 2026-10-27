import EvenPropagation

open Finset
namespace FlatBernoulli
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Increment of the moments of a finite, positive spectral measure. -/
def spectralIncrement (w x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, w i * (x i - 1) * x i ^ (n - 1)

theorem spectralIncrement_odd (w x : ι → ℝ) (m : ℕ) :
    spectralIncrement w x (2*m+1) =
      -(∑ i, (w i*(1-x i)) * (x i^2)^m) := by
  unfold spectralIncrement
  simp only [Nat.add_sub_cancel, pow_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectralIncrement_odd_bound (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ≤ 1)
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i*x i = 0)
    (hthird : spectralIncrement w x 3 ≤ -(1/4)) (m : ℕ) :
    spectralIncrement w x (2*m+1) ≤ -(1/4:ℝ)^m := by
  have hd : ∀ i, 0 ≤ w i*(1-x i) := fun i =>
    mul_nonneg (hw i) (sub_nonneg.mpr (hx i))
  have hdmass : ∑ i, w i*(1-x i) = 1 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hmass, hmean, sub_zero]
  have hthird' := spectralIncrement_odd w x 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd, pow_one] at hthird'
  have hpow := weighted_power_lower (fun i => w i*(1-x i))
    (fun i => x i^2) hd (fun i => sq_nonneg _) hdmass
    (c := (1/4:ℝ)) (by norm_num) (by linarith [hthird']) m
  rw [spectralIncrement_odd]
  linarith

/-- All negative spectral values coincide; repeated copies are harmless. -/
def positiveWeight (w x : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ x i then w i*(1-x i)*x i^11 else 0

def negativeContribution (w x : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ i, if x i < 0 then w i*(1+q)*q^11 else 0

theorem spectralIncrement_even_split (w x : ι → ℝ) {q : ℝ}
    (hq : 0 < q) (hneg : ∀ i, x i < 0 → x i = -q) (m : ℕ) :
    spectralIncrement w x (12+2*m) = q^(2*m)*
      (negativeContribution w x q -
        ∑ i, positiveWeight w x i * ((x i/q)^2)^m) := by
  have hqne : q ≠ 0 := ne_of_gt hq
  unfold spectralIncrement negativeContribution
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ x i
  · simp only [positiveWeight, hi, ite_true, not_lt.mpr hi, ite_false, zero_sub]
    rw [show 12+2*m-1 = 11+2*m by omega, pow_add,
      div_pow, div_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  · have hlt : x i < 0 := lt_of_not_ge hi
    simp only [positiveWeight, hi, ite_false, hlt, ite_true, zero_mul, sub_zero]
    rw [hneg i hlt, show 12+2*m-1 = 11+2*m by omega, pow_add]
    have hp : (-q)^(2*m) = q^(2*m) := (even_two_mul m).neg_pow q
    rw [hp, show (-q)^11 = -q^11 by ring]
    ring

theorem spectralIncrement_even_bound (w x : ι → ℝ) {q c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ≤ 1)
    (hq0 : 1/2 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (hneg : ∀ i, x i < 0 → x i = -q)
    (hbase : spectralIncrement w x 12 ≤ -c)
    (hnext : spectralIncrement w x 14 ≤ spectralIncrement w x 12) (m : ℕ) :
    spectralIncrement w x (12+2*m) ≤ -c*(1/4)^m := by
  have hq : 0 < q := by linarith
  have hw' : ∀ i, 0 ≤ positiveWeight w x i := by
    intro i
    unfold positiveWeight
    split_ifs with hi
    · exact mul_nonneg (mul_nonneg (hw i) (sub_nonneg.mpr (hx i)))
        (pow_nonneg hi 11)
    · rfl
  have hb := spectralIncrement_even_split w x hq hneg 0
  have hn := spectralIncrement_even_split w x hq hneg 1
  norm_num only [Nat.mul_zero, Nat.add_zero, pow_zero, mul_one, one_mul] at hb
  norm_num only [Nat.reduceMul, Nat.reduceAdd, pow_one] at hn
  rw [spectralIncrement_even_split w x hq hneg m]
  apply even_propagation (positiveWeight w x) (fun i => (x i/q)^2)
    hw' (fun i => sq_nonneg _) hq0 hq1 hc
  · simpa only [← hb] using hbase
  · rw [← hn, ← hb]
    exact hnext

theorem spectral_negative_size (w x : ι → ℝ) {q : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ≤ 1) (hq : 0 ≤ q)
    (hneg : ∀ i, x i < 0 → x i = -q)
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i*x i = 0)
    (hsecond : 1/2 ≤ ∑ i, w i*x i^2) : 1/2 ≤ q := by
  have hp : ∀ i, x i^2 ≤ (1-q)*x i+q := by
    intro i
    by_cases hi : x i < 0
    · rw [hneg i hi]
      nlinarith
    · have ht : 0 ≤ (x i+q)*(1-x i) :=
        mul_nonneg (by linarith) (by linarith [hx i])
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hp i) (hw i))
  have he : (∑ i, w i*((1-q)*x i+q)) = q := by
    simp_rw [mul_add, show ∀ i, w i*((1-q)*x i) = (1-q)*(w i*x i) by intro; ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hmean, hmass]
    ring
  rw [he] at hs
  exact hsecond.trans hs

theorem spectralIncrement_tail_negative (w x : ι → ℝ) {q c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ≤ 1)
    (hq0 : 1/2 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (hneg : ∀ i, x i < 0 → x i = -q)
    (hmass : ∑ i, w i = 1) (hmean : ∑ i, w i*x i = 0)
    (hthird : spectralIncrement w x 3 ≤ -(1/4))
    (hbase : spectralIncrement w x 12 ≤ -c)
    (hnext : spectralIncrement w x 14 ≤ spectralIncrement w x 12)
    (n : ℕ) (hn : 11 ≤ n) : spectralIncrement w x n < 0 := by
  obtain ⟨k, he | ho⟩ := Nat.even_or_odd' n
  · have hk : 6 ≤ k := by omega
    have he' : n = 12+2*(k-6) := by omega
    rw [he']
    have h := spectralIncrement_even_bound w x hw hx hq0 hq1 hc hneg hbase hnext (k-6)
    have hp : 0 < c*(1/4:ℝ)^(k-6) := mul_pos hc (pow_pos (by norm_num) _)
    linarith
  · rw [ho]
    have h := spectralIncrement_odd_bound w x hw hx hmass hmean hthird k
    have hp : 0 < (1/4:ℝ)^k := pow_pos (by norm_num) _
    linarith

theorem exists_negative_spectral (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ≤ 1)
    (hmean : ∑ i, w i*x i = 0) (hsecond : 0 < ∑ i, w i*x i^2) :
    ∃ i, x i < 0 := by
  by_contra hn
  have hpos : ∀ i, 0 ≤ x i := by simpa only [not_exists, not_lt] using hn
  have hs : (∑ i, w i*x i^2) ≤ ∑ i, w i*x i := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i)
    nlinarith [hpos i, hx i]
  rw [hmean] at hs
  linarith

end
end FlatBernoulli
