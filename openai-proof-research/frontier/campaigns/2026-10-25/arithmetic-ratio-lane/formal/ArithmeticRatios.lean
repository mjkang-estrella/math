import RealRatios

open Finset
namespace ArithmeticRatios

/-- The integral Dedekind product in §1 of Dimitrov, arXiv:2606.12484v1. -/
def psi (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

/-- Mathlib's divisor-sum function at exponent one. -/
def sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

lemma sigma_eq_sum_divisors (n : ℕ) : sigma n = ∑ d ∈ n.divisors, d := by
  simp [sigma, ArithmeticFunction.sigma_apply]

lemma psi_one : psi 1 = 1 := by simp [psi]

lemma exponent_pos {n p : ℕ} (hp : p ∈ n.primeFactors) : 0 < n.factorization p := by
  have hm := Nat.mem_primeFactors.mp hp
  exact hm.1.factorization_pos_of_dvd hm.2.2 hm.2.1

lemma factor_eq {n p : ℕ} (hp : p ∈ n.primeFactors) :
    p ^ (n.factorization p - 1) * (p + 1) =
      p ^ n.factorization p + p ^ (n.factorization p - 1) := by
  have he : n.factorization p - 1 + 1 = n.factorization p := by
    have := exponent_pos hp
    omega
  rw [mul_add, mul_one, ← pow_succ, he]

lemma self_lt_psi {n : ℕ} (hn : 2 ≤ n) : n < psi n := by
  have hn0 : n ≠ 0 := by omega
  nth_rw 1 [Nat.prod_primeFactors_pow_factorization hn0]
  unfold psi
  apply Finset.prod_lt_prod_of_nonempty₀
  · intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · intro p hp
    rw [factor_eq hp]
    exact Nat.lt_add_of_pos_right (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
  · exact Finset.nonempty_iff_ne_empty.mpr (by
      intro h
      have he := Nat.prod_primeFactors_pow_factorization hn0
      rw [h] at he
      simp only [prod_empty] at he
      omega)

lemma psi_le_sigma {n : ℕ} (hn : n ≠ 0) : psi n ≤ sigma n := by
  unfold psi sigma
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [mul_one]
  apply Finset.prod_le_prod
  intro p hp
  rw [factor_eq hp]
  have he := exponent_pos hp
  have hne : n.factorization p ≠ n.factorization p - 1 := by omega
  have hs : {n.factorization p, n.factorization p - 1} ⊆ range (n.factorization p + 1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [mem_range] <;> omega
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun i _ _ => Nat.zero_le (p ^ i))
  simpa [Finset.sum_pair hne] using hh

end ArithmeticRatios

namespace ArithmeticRatios

/-- Equality with the familiar rational Euler-product formula. -/
theorem psi_euler_product {n : ℕ} (hn : n ≠ 0) :
    (psi n : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)) := by
  have hbase : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [hbase, ← Finset.prod_mul_distrib]
  unfold psi
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have he : n.factorization p - 1 + 1 = n.factorization p := by
    have := exponent_pos hp
    omega
  conv_rhs => rw [← he, pow_succ]
  field_simp

noncomputable def simpleRatio (x y z : ℝ) : ℝ :=
  x / (y+z) + y / (x+z) + z / (x+y)

noncomputable def mixedRatio (x y z : ℝ) : ℝ :=
  simpleRatio (x*(y+z)) (y*(x+z)) (z*(x+y))

lemma simple_scale (x y z c : ℝ) (hc : c ≠ 0) :
    simpleRatio (x*c) (y*c) (z*c) = simpleRatio x y z := by
  simp only [simpleRatio, ← add_mul, mul_div_mul_right _ _ hc]

lemma mixed_scale (x y z c : ℝ) (hc : c ≠ 0) :
    mixedRatio (x*c) (y*c) (z*c) = mixedRatio x y z := by
  unfold mixedRatio
  have h1 : x*c*(y*c+z*c) = (x*(y+z))*(c*c) := by ring
  have h2 : y*c*(x*c+z*c) = (y*(x+z))*(c*c) := by ring
  have h3 : z*c*(x*c+y*c) = (z*(x+y))*(c*c) := by ring
  rw [h1, h2, h3, simple_scale _ _ _ _ (mul_ne_zero hc hc)]

lemma simple_normalize (x y z : ℝ) (hy : y ≠ 0) :
    simpleRatio x y z = RealRatios.simple (x/y) (z/y) := by
  have h := simple_scale x y z y⁻¹ (inv_ne_zero hy)
  simpa [simpleRatio, RealRatios.simple, div_eq_mul_inv, mul_inv_cancel₀ hy] using h.symm

lemma mixed_normalize (x y z : ℝ) (hy : y ≠ 0) :
    mixedRatio x y z = RealRatios.mixed (x/y) (z/y) := by
  have h := mixed_scale x y z y⁻¹ (inv_ne_zero hy)
  have hi : mixedRatio (x/y) 1 (z/y) = RealRatios.mixed (x/y) (z/y) := by
    unfold mixedRatio simpleRatio RealRatios.mixed
    congr 2 <;> ring
  rw [← hi]
  simpa [div_eq_mul_inv, mul_inv_cancel₀ hy] using h.symm

lemma ratio_domain {x y z a b : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (hab : a < b) (hby : b ≤ y) (hyz : y ≤ z) :
    0 < x/y ∧ x/y ≤ a/b ∧ a/b ≤ 1 ∧ 1 ≤ z/y := by
  have ha : 0 < a := hx.trans_le hxa
  have hb : 0 < b := ha.trans hab
  have hy : 0 < y := hb.trans_le hby
  exact ⟨div_pos hx hy, div_le_div₀ ha.le hxa hb hby,
    (div_le_one hb).mpr hab.le, (one_le_div hy).mpr hyz⟩

lemma simple_bound {x y z a b : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (hab : a < b) (hby : b ≤ y) (hyz : y ≤ z) :
    (a^2+a*b+4*b^2)/(2*b*(a+b)) ≤ simpleRatio x y z := by
  obtain ⟨hr, hrq, hq, ht⟩ := ratio_domain hx hxa hab hby hyz
  have ha : 0 < a := hx.trans_le hxa
  have hb : 0 < b := ha.trans hab
  have hy : 0 < y := hb.trans_le hby
  rw [simple_normalize _ _ _ hy.ne']
  have h := RealRatios.simple_normalized_bound hr hrq hq ht
  have he : RealRatios.simple (a/b) 1 = (a^2+a*b+4*b^2)/(2*b*(a+b)) := by
    unfold RealRatios.simple
    field_simp
    ring
  rwa [he] at h

lemma mixed_bound {x y z a b : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (hab : a < b) (hby : b ≤ y) (hyz : y ≤ z) :
    (5*a^2+5*a*b+2*b^2)/((3*a+b)*(a+b)) ≤ mixedRatio x y z := by
  obtain ⟨hr, hrq, hq, ht⟩ := ratio_domain hx hxa hab hby hyz
  have ha : 0 < a := hx.trans_le hxa
  have hb : 0 < b := ha.trans hab
  have hy : 0 < y := hb.trans_le hby
  rw [mixed_normalize _ _ _ hy.ne']
  have h := RealRatios.mixed_normalized_bound hr hrq hq ht
  have he : RealRatios.mixed (a/b) 1 = (5*a^2+5*a*b+2*b^2)/((3*a+b)*(a+b)) := by
    unfold RealRatios.mixed
    field_simp
    ring
  rwa [he] at h

end ArithmeticRatios

namespace ArithmeticRatios

/-- The complete arithmetic-function bridge, before normalization. -/
theorem power_order {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    0 < (Nat.totient n : ℝ)^k ∧
    (Nat.totient n : ℝ)^k ≤ ((n : ℝ)-1)^k ∧
    ((n : ℝ)-1)^k < ((n : ℝ)+1)^k ∧
    ((n : ℝ)+1)^k ≤ (psi n : ℝ)^k ∧
    (psi n : ℝ)^k ≤ (sigma n : ℝ)^k := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hphi : (Nat.totient n : ℝ) ≤ (n : ℝ)-1 := by
    have := Nat.totient_lt n (show 1 < n by omega)
    have : Nat.totient n + 1 ≤ n := this
    have hh : (Nat.totient n : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hpsi : (n : ℝ)+1 ≤ (psi n : ℝ) := by
    exact_mod_cast (show n+1 ≤ psi n from self_lt_psi hn)
  have hsigma : (psi n : ℝ) ≤ (sigma n : ℝ) := by exact_mod_cast psi_le_sigma hn0
  refine ⟨pow_pos hp _, pow_le_pow_left₀ hp.le hphi _, ?_,
    pow_le_pow_left₀ (by linarith) hpsi _, pow_le_pow_left₀ (by positivity) hsigma _⟩
  exact pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)

lemma power_product (n : ℝ) (k : ℕ) :
    (n-1)^k*(n+1)^k = (n^2-1)^k := by rw [← mul_pow]; congr 1; ring

lemma power_square (n : ℝ) (k : ℕ) : (n^k)^2 = n^(2*k) := by
  rw [← pow_mul, Nat.mul_comm]

/-- Dimitrov Conjecture 3 / MathDB 375256, all n ≥ 2 and k ≥ 1.
The general argument was posted by Shivam Patel on 2026-08-20. -/
theorem mathdb_375256 {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (4*((n : ℝ)+1)^(2*k) + ((n : ℝ)^2-1)^k + ((n : ℝ)-1)^(2*k)) /
      (2*(((n : ℝ)+1)^(2*k) + ((n : ℝ)^2-1)^k)) ≤
    (Nat.totient n : ℝ)^k / ((psi n : ℝ)^k + (sigma n : ℝ)^k) +
    (psi n : ℝ)^k / ((Nat.totient n : ℝ)^k + (sigma n : ℝ)^k) +
    (sigma n : ℝ)^k / ((Nat.totient n : ℝ)^k + (psi n : ℝ)^k) := by
  obtain ⟨hx, hxa, hab, hby, hyz⟩ := power_order hn hk
  have h := simple_bound hx hxa hab hby hyz
  have he : 2*((n : ℝ)+1)^k*(((n : ℝ)-1)^k+((n : ℝ)+1)^k) =
      2*(((n : ℝ)+1)^(2*k) + ((n : ℝ)^2-1)^k) := by
    nlinarith only [power_product (n : ℝ) k, power_square ((n : ℝ)+1) k]
  simp only [power_square, power_product, he, simpleRatio] at h
  convert h using 1; ring

/-- Dimitrov Conjecture 9 / MathDB 375257, all n ≥ 2 and k ≥ 1.
The general argument and positive polynomial certificate were posted by
Shivam Patel on 2026-08-20. -/
theorem mathdb_375257 {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (5*((n : ℝ)-1)^(2*k) + 5*((n : ℝ)^2-1)^k + 2*((n : ℝ)+1)^(2*k)) /
      ((3*((n : ℝ)-1)^k + ((n : ℝ)+1)^k)*(((n : ℝ)-1)^k + ((n : ℝ)+1)^k)) ≤
    (Nat.totient n : ℝ)^k*((psi n : ℝ)^k+(sigma n : ℝ)^k) /
      ((psi n : ℝ)^k*((Nat.totient n : ℝ)^k+(sigma n : ℝ)^k) +
        (sigma n : ℝ)^k*((Nat.totient n : ℝ)^k+(psi n : ℝ)^k)) +
    (psi n : ℝ)^k*((Nat.totient n : ℝ)^k+(sigma n : ℝ)^k) /
      ((Nat.totient n : ℝ)^k*((psi n : ℝ)^k+(sigma n : ℝ)^k) +
        (sigma n : ℝ)^k*((Nat.totient n : ℝ)^k+(psi n : ℝ)^k)) +
    (sigma n : ℝ)^k*((Nat.totient n : ℝ)^k+(psi n : ℝ)^k) /
      ((Nat.totient n : ℝ)^k*((psi n : ℝ)^k+(sigma n : ℝ)^k) +
        (psi n : ℝ)^k*((Nat.totient n : ℝ)^k+(sigma n : ℝ)^k)) := by
  obtain ⟨hx, hxa, hab, hby, hyz⟩ := power_order hn hk
  have h := mixed_bound hx hxa hab hby hyz
  simp only [power_square, mixedRatio, simpleRatio] at h
  have he : 5*((n : ℝ)-1)^k*((n : ℝ)+1)^k = 5*((n : ℝ)^2-1)^k := by
    rw [mul_assoc, power_product]
  rwa [he] at h

end ArithmeticRatios
