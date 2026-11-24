# Lean source appendix — MathDB 360458

COMPLETE: `Guo62.guo_conj_6_2`, with the fixed literal review statement. All modules below are byte-identical to src/.

### `GuoAlgebra.lean`

```lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/- A kernel-checkable abstract core of the new block-lifting argument.
   This is a helper, NOT the source endpoint or a separate result. -/
namespace GuoBlockLift

/-- Complementary errors average to a constant when the weights are invariant
under the same involution. No division by the total weight is needed. -/
theorem weighted_involution_average
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (σ : Equiv.Perm ι) (t L : ι → K) (c : K)
    (ht : ∀ i, t (σ i) = t i)
    (hL : ∀ i, L i + L (σ i) = c) :
    2 * (∑ i, t i * L i) = c * ∑ i, t i := by
  have hs : (∑ i, t i * L (σ i)) = ∑ i, t i * L i := by
    calc
      (∑ i, t i * L (σ i)) = ∑ i, t (σ i) * L (σ i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ht]
      _ = ∑ i, t i * L i := Equiv.sum_comp σ (fun i => t i * L i)
  calc
    2 * (∑ i, t i * L i) =
        (∑ i, t i * L i) + ∑ i, t i * L (σ i) := by rw [hs]; ring
    _ = ∑ i, t i * (L i + L (σ i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, t i * c := by simp_rw [hL]
    _ = c * ∑ i, t i := by rw [← Finset.sum_mul]; ring

/-- The numerical identity that cancels the reflected average against the
whole-block core derivative. -/
theorem core_constant_cancels {K : Type*} [Field K]
    (n h H : K) (hh : 2 * h = n - 1) :
    3 * (-n^2 - 4*n*H) + n + 2*n*(1 + 3*h + 6*H) = 0 := by
  calc
    3 * (-n^2 - 4*n*H) + n + 2*n*(1 + 3*h + 6*H) =
        3*n*(2*h - (n-1)) := by ring
    _ = 0 := by rw [hh]; ring

/-- Equations (5)--(8) imply zero total derivative correction. -/
theorem block_error_sum_zero
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (σ : Equiv.Perm ι) (t L : ι → K) (n h H : K)
    (ht : ∀ i, t (σ i) = t i)
    (hL : ∀ i, L i + L (σ i) = 1 + 3*h + 6*H)
    (hh : 2*h = n-1) :
    ∑ i, t i * (3*(-n^2 - 4*n*H) + n + 4*n*L i) = 0 := by
  have havg := weighted_involution_average σ t L (1+3*h+6*H) ht hL
  have hc := core_constant_cancels n h H hh
  have hexpand :
      (∑ i, t i * (3*(-n^2 - 4*n*H) + n + 4*n*L i)) =
      (3*(-n^2 - 4*n*H) + n) * (∑ i, t i) +
      2*n*(2*(∑ i, t i * L i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand, havg]
  calc
    (3*(-n^2 - 4*n*H) + n) * (∑ i, t i) +
        2*n*((1+3*h+6*H)*(∑ i, t i)) =
        (3*(-n^2 - 4*n*H)+n+2*n*(1+3*h+6*H))*(∑ i, t i) := by ring
    _ = 0 := by rw [hc]; ring

/-- Cleared form of the finite q-Dixon telescoping certificate (11). -/
theorem finite_dixon_certificate {K : Type*} [CommRing K] (q w x : K) :
    (1+w) * (q*(1-q^2*x)*(w-x)*(1-w*x) -
      (1-x)*(1-q^2*w*x)*(w-q^2*x)) =
    (q*w-1)*(1+q*x)*(1-w*x)*(w-q^2*x) +
      (1+q*x)*(q-w)*(w-x)*(1-q^2*w*x) := by
  ring

/-- Standard algebraic bridge from value-and-derivative divisibility to a
square factor. The source application still needs its root-evaluation lemmas. -/
theorem square_dvd_of_dvd_derivative
    {K : Type*} [Field K] (p f : Polynomial K)
    (hp : IsCoprime p p.derivative)
    (hf : p ∣ f) (hdf : p ∣ f.derivative) : p^2 ∣ f := by
  obtain ⟨g, rfl⟩ := hf
  rw [Polynomial.derivative_mul] at hdf
  have hpg : p ∣ p * g.derivative := dvd_mul_right p g.derivative
  have hprod : p ∣ p.derivative * g := by
    have hs := dvd_sub hdf hpg
    simpa only [add_sub_cancel_right] using hs
  obtain ⟨a, ha⟩ := hp.dvd_of_dvd_mul_left hprod
  refine ⟨a, ?_⟩
  rw [ha]
  ring

#print axioms square_dvd_of_dvd_derivative
#print axioms finite_dixon_certificate
#print axioms block_error_sum_zero
end GuoBlockLift
```

### `GuoReciprocity.lean`

```lean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Exact finite-product reflection. This is an identity at an independent
shift parameter, so its later first-order specialization is legitimate. -/
namespace Guo62
section Products
variable {K : Type*} [CommRing K]

def prefixProd (a : ℕ → K) (s : ℕ) : K := ∏ j ∈ Finset.range s, a j

/-- Complementary reversed factors telescope without division by a sum, or even
by a product. The hypotheses concern individual factors only. -/
theorem prefixProd_complement (a b : ℕ → K) (h s : ℕ) (hs : s ≤ h)
    (hab : ∀ j < s, a (h-1-j) * b j = 1) :
    prefixProd a (h-s) = prefixProd a h * prefixProd b s := by
  have hsplit : prefixProd a h = prefixProd a (h-s) *
      (∏ j ∈ Finset.range s, a (h-s+j)) := by
    simpa [prefixProd, Nat.sub_add_cancel hs] using Finset.prod_range_add a (h-s) s
  have hpair : (∏ j ∈ Finset.range s, a (h-s+j)) * prefixProd b s = 1 := by
    rw [prefixProd, ← Finset.prod_range_reflect b s, ← Finset.prod_mul_distrib]
    have he : (∏ j ∈ Finset.range s, a (h-s+j) * b (s-1-j)) =
        ∏ j ∈ Finset.range s, (1 : K) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hh : h-1-(s-1-j) = h-s+j := by omega
      simpa only [hh] using hab (s-1-j) (by omega)
    rw [he]
    simp
  rw [hsplit, mul_assoc, hpair, mul_one]

end Products
section Field
variable {K : Type*} [Field K]

/-- The local algebra behind reversal of q-Pochhammer quotients. All four
potentially singular factors are explicitly controlled. -/
lemma reciprocal_pair (u A B : K) (hu : u ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (h1 : 1-u*A ≠ 0) (h2 : 1-u*B ≠ 0) :
    ((1-u*B)/(1-u*A)) * ((A/B)*((1-u⁻¹*A⁻¹)/(1-u⁻¹*B⁻¹))) = 1 := by
  have h3 : 1-u⁻¹*B⁻¹ ≠ 0 := by
    have he : 1-u⁻¹*B⁻¹ = (u*B-1)/(u*B) := by
      field_simp
    rw [he]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h2))) (mul_ne_zero hu hB)
  field_simp
  apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h2)))).mpr
  ring

/-- Quotients in the shift parameter; negative exponents are integer powers. -/
def shiftRatio (Q u : K) (h s : ℕ) : K :=
  prefixProd (fun j => (1-u*Q^((j:ℤ)-(h:ℤ))) / (1-u*Q^((j:ℤ)+1))) s

/-- Exact shift-parameter reflection for the Pochhammer ratio. The two
non-vanishing hypotheses are explicit, and concern only the s reversed factors. -/
theorem shiftRatio_reflection (Q u : K) (h s : ℕ) (hQ : Q ≠ 0) (hu : u ≠ 0)
    (hs : s ≤ h)
    (hA : ∀ j < s, 1-u*Q^((h:ℤ)-(j:ℤ)) ≠ 0)
    (hB : ∀ j < s, 1-u*Q^(-1-(j:ℤ)) ≠ 0) :
    shiftRatio Q u h (h-s) =
      shiftRatio Q u h h * (Q^((h:ℤ)+1))^s * shiftRatio Q u⁻¹ h s := by
  let a : ℕ → K := fun j => (1-u*Q^((j:ℤ)-(h:ℤ))) / (1-u*Q^((j:ℤ)+1))
  let b : ℕ → K := fun j => Q^((h:ℤ)+1) *
    ((1-u⁻¹*Q^((j:ℤ)-(h:ℤ))) / (1-u⁻¹*Q^((j:ℤ)+1)))
  have hab : ∀ j < s, a (h-1-j)*b j = 1 := by
    intro j hj
    have hjh : j < h := lt_of_lt_of_le hj hs
    have he : ((h-1-j : ℕ):ℤ) = (h:ℤ)-1-j := by omega
    have hq : Q^((h:ℤ)-(j:ℤ)) / Q^(-1-(j:ℤ)) = Q^((h:ℤ)+1) := by
      rw [← zpow_sub₀ hQ]
      congr 1
      ring
    have hiA : (Q^((h:ℤ)-(j:ℤ)))⁻¹ = Q^((j:ℤ)-(h:ℤ)) := by
      rw [← zpow_neg]
      congr 1
      ring
    have hiB : (Q^(-1-(j:ℤ)))⁻¹ = Q^((j:ℤ)+1) := by
      rw [← zpow_neg]
      congr 1
      ring
    have hp := reciprocal_pair u (Q^((h:ℤ)-(j:ℤ))) (Q^(-1-(j:ℤ))) hu
      (zpow_ne_zero _ hQ) (zpow_ne_zero _ hQ) (hA j hj) (hB j hj)
    rw [hq, hiA, hiB] at hp
    dsimp only [a, b]
    rw [he, show (h:ℤ)-1-j-h = -1-j by ring, show (h:ℤ)-1-j+1 = h-j by ring]
    exact hp
  have hp := prefixProd_complement a b h s hs hab
  have hb : prefixProd b s = (Q^((h:ℤ)+1))^s * shiftRatio Q u⁻¹ h s := by
    simp [prefixProd, b, shiftRatio, Finset.prod_mul_distrib]
  rw [hb] at hp
  simpa only [shiftRatio, a, mul_assoc] using hp

/-- The actual weighted shifted summand at an independent parameter u. -/
def shiftTerm (z Q u : K) (h s : ℕ) : K :=
  (1+u*z*Q^s)/(1+z) * z^s * (shiftRatio Q u h s)^3

def shiftSum (z Q u : K) (h : ℕ) : K :=
  ∑ s ∈ Finset.range (h+1), shiftTerm z Q u h s

/-- Termwise reciprocity of the complete weighted half-block. Root-order
consequences are explicit hypotheses here; the endpoint has no such hypotheses. -/
theorem shiftTerm_reflection (z Q u : K) (h s : ℕ)
    (hz : z ≠ 0) (hQ : Q ≠ 0) (hu : u ≠ 0) (hs : s ≤ h)
    (hQ4 : Q = z^4) (hQh : Q^h = (z^2)⁻¹) (hQh1 : Q^(h+1) = z^2)
    (hA : ∀ j < s, 1-u*Q^((h:ℤ)-(j:ℤ)) ≠ 0)
    (hB : ∀ j < s, 1-u*Q^(-1-(j:ℤ)) ≠ 0) :
    shiftTerm z Q u h (h-s) =
      (u*(z^h/z)*(shiftRatio Q u h h)^3) * shiftTerm z Q u⁻¹ h s := by
  have hr := shiftRatio_reflection Q u h s hQ hu hs hA hB
  have hc : (Q^((h:ℤ)+1))^s = (z^s)^2 := by
    rw [show (h:ℤ)+1 = ((h+1:ℕ):ℤ) by omega, zpow_natCast, hQh1]
    rw [← pow_mul, Nat.mul_comm 2 s, pow_mul]
  rw [hc] at hr
  dsimp only [shiftTerm]
  rw [hr, pow_sub₀ Q hQ hs, pow_sub₀ z hz hs, hQh, hQ4]
  have hpow : (z^4)^s = (z^s)^4 := by rw [← pow_mul, Nat.mul_comm 4 s, pow_mul]
  rw [hpow]
  field_simp
  ring

/-- Exact reciprocity of the finite sum, not a root-only equality that would be
invalid to differentiate. No division by this sum occurs. -/
theorem shiftSum_reciprocity (z Q u : K) (h : ℕ)
    (hz : z ≠ 0) (hQ : Q ≠ 0) (hu : u ≠ 0)
    (hQ4 : Q = z^4) (hQh : Q^h = (z^2)⁻¹) (hQh1 : Q^(h+1) = z^2)
    (hA : ∀ j < h, 1-u*Q^((h:ℤ)-(j:ℤ)) ≠ 0)
    (hB : ∀ j < h, 1-u*Q^(-1-(j:ℤ)) ≠ 0) :
    shiftSum z Q u h =
      (u*(z^h/z)*(shiftRatio Q u h h)^3) * shiftSum z Q u⁻¹ h := by
  unfold shiftSum
  rw [← Finset.sum_range_reflect (fun s => shiftTerm z Q u h s) (h+1)]
  simp only [Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsh : s ≤ h := by have := Finset.mem_range.mp hs; omega
  exact shiftTerm_reflection z Q u h s hz hQ hu hsh hQ4 hQh hQh1
    (fun j hj => hA j (lt_of_lt_of_le hj hsh))
    (fun j hj => hB j (lt_of_lt_of_le hj hsh))

#print axioms prefixProd_complement
#print axioms shiftRatio_reflection
#print axioms shiftTerm_reflection
#print axioms shiftSum_reciprocity

end Field
end Guo62
```

### `GuoStatement.lean`

```lean
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-! Literal objects required by the independent review of MathDB 360458.
`GuoConjecture62` is a proposition, not an assertion that it has been proved. -/
namespace Guo62
open Polynomial
noncomputable section

abbrev q : RatFunc ℚ := RatFunc.X

def poch (a d k : ℕ) : RatFunc ℚ :=
  ∏ j ∈ Finset.range k, (1 - q^(a + d*j))
def qInt2 (n : ℕ) : RatFunc ℚ := ∑ i ∈ Finset.range n, q^(2*i)
def halfPoch (k : ℕ) : ℚ := ∏ j ∈ Finset.range k, ((1:ℚ)/2 + j)
def CongSq (n : ℕ) (f g : RatFunc ℚ) : Prop :=
  IsCoprime (cyclotomic n ℚ) f.denom ∧ IsCoprime (cyclotomic n ℚ) g.denom ∧
  (cyclotomic n ℚ)^2 ∣ (f - g).num

def lhs (m n : ℕ) : RatFunc ℚ :=
  ∑ k ∈ Finset.range (m*n),
    (1 + q^(4*k+1)) * (poch 2 4 k)^3 * q^k / ((1 + q) * (poch 4 4 k)^3)
def rhs (m n : ℕ) : RatFunc ℚ :=
  qInt2 n * poch 3 4 ((n-1)/2) / poch 5 4 ((n-1)/2) * (q^((n-1)/2))⁻¹ *
    ((∑ k ∈ Finset.range m, (halfPoch k)^3 / (Nat.factorial k : ℚ)^3 : ℚ) : RatFunc ℚ)

def GuoConjecture62 : Prop :=
  ∀ (m n : ℕ), 0 < m → 1 < n → n % 4 = 1 → CongSq n (lhs m n) (rhs m n)

/-- Polynomial representatives of the finite q-Pochhammer products. -/
def pochPoly (a d k : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range k, (1 - X^(a + d*j))

lemma pochPoly_map (a d k : ℕ) :
    algebraMap ℚ[X] (RatFunc ℚ) (pochPoly a d k) = poch a d k := by
  simp [pochPoly, poch, map_prod, RatFunc.algebraMap_X]

lemma one_sub_X_pow_ne_zero {a : ℕ} (ha : 0 < a) : (1 - X^a : ℚ[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) h
  simp [coeff_X_pow, (Nat.ne_of_gt ha).symm] at hc

lemma one_add_X_pow_ne_zero (a : ℕ) : (1 + X^a : ℚ[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) h
  by_cases ha : a = 0
  · subst a; norm_num at hc
  · simp [coeff_X_pow, Ne.symm ha] at hc

lemma one_sub_q_pow_ne_zero {a : ℕ} (ha : 0 < a) : (1 - q^a) ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero (one_sub_X_pow_ne_zero ha)
  simpa [map_sub, map_pow, RatFunc.algebraMap_X] using h

lemma one_add_q_pow_ne_zero (a : ℕ) : (1 + q^a) ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero (one_add_X_pow_ne_zero a)
  simpa [map_add, map_pow, RatFunc.algebraMap_X] using h

lemma one_add_q_ne_zero : (1 + q) ≠ 0 := by
  simpa using one_add_q_pow_ne_zero 1

lemma q_pow_ne_zero (a : ℕ) : q^a ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero

lemma poch_ne_zero {a : ℕ} (ha : 0 < a) (d k : ℕ) : poch a d k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact one_sub_q_pow_ne_zero (by omega)

lemma lhs_denominator_ne_zero (k : ℕ) : (1 + q) * (poch 4 4 k)^3 ≠ 0 :=
  mul_ne_zero one_add_q_ne_zero (pow_ne_zero _ (poch_ne_zero (by decide) 4 k))

lemma rhs_poch_denominator_ne_zero (n : ℕ) : poch 5 4 ((n-1)/2) ≠ 0 :=
  poch_ne_zero (by decide) 4 _

lemma factorial_denominator_ne_zero (k : ℕ) : (Nat.factorial k : ℚ)^3 ≠ 0 := by
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))

/-- This certifies *all* the divisions and inverses in the literal endpoint.
It asserts non-vanishing in ℚ(q), not evaluation at a root of unity. -/
theorem endpoint_denominators_nonzero (m n : ℕ) :
    (∀ k ∈ Finset.range (m*n), (1 + q) * (poch 4 4 k)^3 ≠ 0) ∧
    poch 5 4 ((n-1)/2) ≠ 0 ∧ q^((n-1)/2) ≠ 0 ∧
    (∀ k ∈ Finset.range m, (Nat.factorial k : ℚ)^3 ≠ 0) ∧ (2 : ℚ) ≠ 0 := by
  exact ⟨fun k _ => lhs_denominator_ne_zero k, rhs_poch_denominator_ne_zero n,
    q_pow_ne_zero _, fun k _ => factorial_denominator_ne_zero k, by decide⟩

lemma halfPoch_pos (k : ℕ) : 0 < halfPoch k := by
  apply Finset.prod_pos
  intro j _
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  exact add_pos_of_pos_of_nonneg (by norm_num) hj

lemma admissible_half (n : ℕ) (hn : 1 < n) (h4 : n % 4 = 1) :
    2 * ((n-1)/2) = n-1 ∧ Even ((n-1)/2) ∧ 5 ≤ n := by
  have he : (n-1)/2 = 2*(n/4) := by omega
  refine ⟨by omega, ?_, by omega⟩
  exact ⟨n/4, by omega⟩

#print GuoConjecture62
#print axioms endpoint_denominators_nonzero
#print axioms pochPoly_map
#print axioms admissible_half
end
end Guo62
```

### `GuoCongruence.lean`

```lean
import GuoStatement
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Polynomial witnesses for regular rational functions. No root evaluation of
an uncancelled quotient is used in this interface. -/
namespace Guo62
open Polynomial
noncomputable section

abbrev embed : ℚ[X] →+* RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ)

def Regular (p : ℚ[X]) (f : RatFunc ℚ) : Prop := IsCoprime p f.denom

lemma regular_of_fraction {p A B : ℚ[X]} (_hB : B ≠ 0) (hpB : IsCoprime p B) :
    Regular p (embed A / embed B) := by
  exact hpB.of_isCoprime_of_dvd_right (RatFunc.denom_div_dvd A B)

/-- Regularity is precisely existence of a representative with unit denominator
at p. Both directions refer to the actual reduced RatFunc denominator. -/
theorem regular_iff_fraction (p : ℚ[X]) (f : RatFunc ℚ) :
    Regular p f ↔ ∃ A B : ℚ[X], B ≠ 0 ∧ IsCoprime p B ∧ f = embed A / embed B := by
  constructor
  · intro h
    exact ⟨f.num, f.denom, RatFunc.denom_ne_zero f, h, (RatFunc.num_div_denom f).symm⟩
  · rintro ⟨A, B, hB, hpB, rfl⟩
    exact regular_of_fraction hB hpB

/-- If a denominator is a unit at p, reduction of the fraction cannot change
whether p^e divides the numerator. -/
theorem pow_dvd_num_fraction_iff (p A B : ℚ[X]) (e : ℕ)
    (hB : B ≠ 0) (hpB : IsCoprime p B) :
    p^e ∣ (embed A / embed B).num ↔ p^e ∣ A := by
  let f := embed A / embed B
  have hcross : f.num * B = A * f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hB).mpr rfl
  have hreg : IsCoprime p f.denom := regular_of_fraction hB hpB
  constructor
  · intro h
    have hd : p^e ∣ A * f.denom := hcross ▸ dvd_mul_of_dvd_left h B
    exact (hreg.pow_left).dvd_of_dvd_mul_right hd
  · intro h
    have hd : p^e ∣ f.num * B := hcross.symm ▸ dvd_mul_of_dvd_left h f.denom
    exact (hpB.pow_left).dvd_of_dvd_mul_right hd

lemma sub_fractions (A B C D : ℚ[X]) (hB : B ≠ 0) (hD : D ≠ 0) :
    embed A / embed B - embed C / embed D =
      embed (A*D-C*B) / embed (B*D) := by
  simp only [map_mul, map_sub]
  simpa only [mul_comm (embed C) (embed B)] using
    div_sub_div (embed A) (embed C) (RatFunc.algebraMap_ne_zero hB) (RatFunc.algebraMap_ne_zero hD)

/-- Faithful cleared-numerator bridge to the review's exact CongSq predicate.
The coprimality hypotheses must be established after cancelling singular factors. -/
theorem congSq_fractions_iff (n : ℕ) (A B C D : ℚ[X])
    (hB : B ≠ 0) (hD : D ≠ 0)
    (hpB : IsCoprime (cyclotomic n ℚ) B)
    (hpD : IsCoprime (cyclotomic n ℚ) D) :
    CongSq n (embed A / embed B) (embed C / embed D) ↔
      (cyclotomic n ℚ)^2 ∣ A*D-C*B := by
  rw [CongSq, sub_fractions A B C D hB hD,
    pow_dvd_num_fraction_iff _ _ _ 2 (mul_ne_zero hB hD) (hpB.mul_right hpD)]
  exact and_iff_right (regular_of_fraction hB hpB) |>.trans
    (and_iff_right (regular_of_fraction hD hpD))

lemma Regular.zero (p : ℚ[X]) : Regular p 0 := by simpa only [Regular, RatFunc.denom_zero] using (isCoprime_one_right : IsCoprime p 1)
lemma Regular.one (p : ℚ[X]) : Regular p 1 := by simpa only [Regular, RatFunc.denom_one] using (isCoprime_one_right : IsCoprime p 1)
lemma Regular.poly (p A : ℚ[X]) : Regular p (embed A) := by simpa only [Regular, embed, RatFunc.denom_algebraMap] using (isCoprime_one_right : IsCoprime p 1)

lemma Regular.add {p : ℚ[X]} {f g : RatFunc ℚ}
    (hf : Regular p f) (hg : Regular p g) : Regular p (f+g) :=
  (hf.mul_right hg).of_isCoprime_of_dvd_right (RatFunc.denom_add_dvd f g)

lemma Regular.mul {p : ℚ[X]} {f g : RatFunc ℚ}
    (hf : Regular p f) (hg : Regular p g) : Regular p (f*g) :=
  (hf.mul_right hg).of_isCoprime_of_dvd_right (RatFunc.denom_mul_dvd f g)

lemma Regular.neg {p : ℚ[X]} {f : RatFunc ℚ} (hf : Regular p f) : Regular p (-f) := by
  have h := (Regular.poly p (-1)).mul hf
  simpa using h

lemma Regular.sub {p : ℚ[X]} {f g : RatFunc ℚ}
    (hf : Regular p f) (hg : Regular p g) : Regular p (f-g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma Regular.sum {ι : Type*} (s : Finset ι) {p : ℚ[X]} (f : ι → RatFunc ℚ)
    (hf : ∀ i ∈ s, Regular p (f i)) : Regular p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Regular.zero p
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Reduced numerators divisible by p^e are closed under addition *when the
summands are regular*. This excludes a hidden cancellation of p-poles. -/
lemma pow_dvd_num_add {p : ℚ[X]} {f g : RatFunc ℚ} (e : ℕ)
    (hf : Regular p f) (hg : Regular p g)
    (hfn : p^e ∣ f.num) (hgn : p^e ∣ g.num) : p^e ∣ (f+g).num := by
  have hc := RatFunc.num_denom_add f g
  have hn : p^e ∣ (f.num*g.denom+f.denom*g.num) :=
    dvd_add (dvd_mul_of_dvd_left hfn _) (dvd_mul_of_dvd_right hgn _)
  have hd : p^e ∣ (f+g).num * (f.denom*g.denom) :=
    hc.symm ▸ dvd_mul_of_dvd_left hn _
  exact ((hf.mul_right hg).pow_left).dvd_of_dvd_mul_right hd

lemma pow_dvd_num_mul {p : ℚ[X]} {f g : RatFunc ℚ} (e : ℕ)
    (hf : Regular p f) (hg : Regular p g) (hfn : p^e ∣ f.num) :
    p^e ∣ (f*g).num := by
  have hc := RatFunc.num_denom_mul f g
  have hd : p^e ∣ (f*g).num * (f.denom*g.denom) :=
    hc.symm ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hfn g.num) _
  exact ((hf.mul_right hg).pow_left).dvd_of_dvd_mul_right hd

#print axioms regular_iff_fraction
#print axioms pow_dvd_num_fraction_iff
#print axioms congSq_fractions_iff
end
end Guo62
```

### `GuoFirstOrder.lean`

```lean
import GuoAlgebra
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Fin

/-! Concrete half-block first-order cancellation. These are conditional
algebraic lemmas: the actual full-block derivatives still have to be computed. -/
namespace Guo62
section
variable {K : Type*} [Field K] [CharZero K]

/-- Reflected shift errors cancel on the source's actual interval [0,h].
There is no hypothesis that the total summand value is nonzero. -/
theorem half_block_error_zero (h : ℕ) (n H : K) (t L : ℕ → K)
    (hh : 2*(h:K) = n-1)
    (ht : ∀ s ≤ h, t (h-s) = t s)
    (hL : ∀ s ≤ h, L s + L (h-s) = 1+3*(h:K)+6*H) :
    ∑ s ∈ Finset.range (h+1), t s * (3*(-n^2-4*n*H)+n+4*n*L s) = 0 := by
  have he := GuoBlockLift.block_error_sum_zero (Fin.revPerm (n := h+1))
    (fun s : Fin (h+1) => t s.val) (fun s : Fin (h+1) => L s.val)
    n (h:K) H
    (fun s => by simpa using ht s.val (by omega))
    (fun s => by simpa using hL s.val (by omega)) hh
  rw [Finset.sum_fin_eq_sum_range] at he
  have heq : (∑ s ∈ Finset.range (h+1),
      if hs : s < h+1 then t s*(3*(-n^2-4*n*H)+n+4*n*L s) else 0) =
      ∑ s ∈ Finset.range (h+1), t s*(3*(-n^2-4*n*H)+n+4*n*L s) := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [dite_eq_left (Finset.mem_range.mp hs)]
  rw [heq] at he
  exact he

/-- Given the computed per-term derivative shift, the concrete sum of first
derivatives is unchanged after multiplication by the classical block value. -/
theorem first_order_block_assembly (h : ℕ) (n H ell c : K)
    (t L d shiftedD : ℕ → K)
    (hh : 2*(h:K) = n-1)
    (ht : ∀ s ≤ h, t (h-s) = t s)
    (hL : ∀ s ≤ h, L s + L (h-s) = 1+3*(h:K)+6*H)
    (hd : ∀ s ≤ h, shiftedD s = c^3 *
      (d s + ell*t s*(3*(-n^2-4*n*H)+n+4*n*L s))) :
    (∑ s ∈ Finset.range (h+1), shiftedD s) =
      c^3 * ∑ s ∈ Finset.range (h+1), d s := by
  have herr := half_block_error_zero h n H t L hh ht hL
  calc
    _ = ∑ s ∈ Finset.range (h+1), (c^3*d s +
        (c^3*ell)*(t s*(3*(-n^2-4*n*H)+n+4*n*L s))) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hd s (by have := Finset.mem_range.mp hs; omega)]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, herr]
      ring

end
#print axioms half_block_error_zero
#print axioms first_order_block_assembly
end Guo62
```

### `GuoProducts.lean`

```lean
import GuoStatement
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Guo62
noncomputable section
open Polynomial

/-- The sum form of the source q-integer agrees with its fraction form, and
the latter's denominator is visibly nonzero. -/
theorem qInt2_eq_fraction (n : ℕ) :
    qInt2 n = (1-q^(2*n))/(1-q^2) := by
  apply (eq_div_iff (one_sub_q_pow_ne_zero (by decide))).mpr
  have h := geom_sum_mul_neg (q^2) n
  simpa only [qInt2, ← pow_mul] using h

/-- General geometric cancellation of the common vanishing factor 1-x.
The representative on the right remains evaluable at x=1. -/
theorem geometric_cancel {K : Type*} [Field K] (x : K) (a b : ℕ)
    (hx : x ≠ 1) (_hb : (∑ j ∈ Finset.range b, x^j) ≠ 0) :
    (1-x^a)/(1-x^b) =
      (∑ j ∈ Finset.range a, x^j)/(∑ j ∈ Finset.range b, x^j) := by
  have he (k : ℕ) : 1-x^k = (∑ j ∈ Finset.range k, x^j)*(1-x) :=
    (geom_sum_mul_neg x k).symm
  rw [he a, he b, mul_div_mul_right]
  exact sub_ne_zero.mpr (Ne.symm hx)

/-- q-Pochhammer splitting, retaining the source's arithmetic progression. -/
theorem poch_add (a d k l : ℕ) :
    poch a d (k+l) = poch a d k * poch (a+d*k) d l := by
  rw [poch, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  ring

/-- Literal rising half-factorial satisfies the expected recurrence. -/
lemma halfPoch_succ (k : ℕ) : halfPoch (k+1) = halfPoch k * ((1:ℚ)/2+k) := by
  exact Finset.prod_range_succ _ _

/-- A division-free recurrence for the classical coefficient in the review.
This avoids introducing a binomial-coefficient normalization bridge. -/
lemma half_ratio_step (k : ℕ) :
    halfPoch (k+1) / (Nat.factorial (k+1) : ℚ) =
      (halfPoch k / (Nat.factorial k : ℚ)) * ((2*k+1:ℚ)/(2*k+2)) := by
  rw [halfPoch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk : (k:ℚ)+1 ≠ 0 := by positivity
  have hk' : (2*(k:ℚ)+2) ≠ 0 := by positivity
  field_simp
  ring

#print axioms qInt2_eq_fraction
#print axioms geometric_cancel
#print axioms poch_add
end
end Guo62
```

### `GuoRoots.lean`

```lean
import GuoAlgebra
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Cyclotomic divisibility is detected at a genuine primitive root. Because
coefficients are rational, one primitive root suffices (minimal polynomial). -/
namespace Guo62
open Polynomial
section
variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {ζ : K}

lemma cyclotomic_dvd_iff_aeval_zero (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (P : ℚ[X]) :
    cyclotomic n ℚ ∣ P ↔ aeval ζ P = 0 := by
  rw [cyclotomic_eq_minpoly_rat hζ hn, minpoly.dvd_iff]

/-- Multiplicity two, with both value and formal derivative checked at the
same primitive root; no analytic root enumeration is necessary. -/
theorem cyclotomic_square_dvd_of_aeval_zero (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (P : ℚ[X]) (hv : aeval ζ P = 0) (hd : aeval ζ P.derivative = 0) :
    (cyclotomic n ℚ)^2 ∣ P := by
  have : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  exact GuoBlockLift.square_dvd_of_dvd_derivative _ _
    (separable_cyclotomic n ℚ)
    ((cyclotomic_dvd_iff_aeval_zero hn hζ P).mpr hv)
    ((cyclotomic_dvd_iff_aeval_zero hn hζ P.derivative).mpr hd)

lemma coprime_cyclotomic_of_aeval_ne_zero (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (P : ℚ[X]) (hP : aeval ζ P ≠ 0) : IsCoprime (cyclotomic n ℚ) P := by
  rw [(cyclotomic.irreducible_rat hn).coprime_iff_not_dvd]
  exact fun hd => hP ((cyclotomic_dvd_iff_aeval_zero hn hζ P).mp hd)

omit [CharZero K] in
lemma one_sub_root_pow_ne_zero (hζ : IsPrimitiveRoot ζ n) {a : ℕ} (ha : ¬ n ∣ a) :
    1-ζ^a ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm (fun h => ha ((hζ.pow_eq_one_iff_dvd a).mp h)))

lemma binomial_coprime_cyclotomic (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    {a : ℕ} (ha : ¬ n ∣ a) : IsCoprime (cyclotomic n ℚ) (1-X^a) := by
  apply coprime_cyclotomic_of_aeval_ne_zero hn hζ
  simpa using one_sub_root_pow_ne_zero hζ ha

/-- No power of an odd-order root is -1 in characteristic zero. -/
lemma one_add_root_pow_ne_zero (hn : Odd n) (hζ : IsPrimitiveRoot ζ n) (a : ℕ) :
    1+ζ^a ≠ 0 := by
  intro hz
  have ha : ζ^a = -1 := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)
  have hr : (ζ^a)^n = 1 := by rw [← pow_mul, Nat.mul_comm a n, pow_mul, hζ.pow_eq_one, one_pow]
  rw [ha, hn.neg_one_pow] at hr
  norm_num at hr

lemma plus_binomial_coprime_cyclotomic (hn : 0 < n) (ho : Odd n)
    (hζ : IsPrimitiveRoot ζ n) (a : ℕ) :
    IsCoprime (cyclotomic n ℚ) (1+X^a) := by
  apply coprime_cyclotomic_of_aeval_ne_zero hn hζ
  simpa using one_add_root_pow_ne_zero ho hζ a

omit [CharZero K] in
lemma fourth_power_primitive (ho : Odd n) (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (ζ^4) n := by
  apply hζ.pow_of_coprime 4
  simpa using ho.coprime_two_left.pow_left 2

/- Root relations used in exact shift reciprocity; only n=2h+1 is needed. -/
omit [CharZero K] in
lemma root_half_relations (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (h : ℕ) (hhalf : n = 2*h+1) :
    (ζ^4)^h = (ζ^2)⁻¹ ∧ (ζ^4)^(h+1) = ζ^2 := by
  have hz : ζ ≠ 0 := hζ.ne_zero hn.ne'
  have hmul : (ζ^4)^h * ζ^2 = 1 := by
    rw [← pow_mul, ← pow_add, show 4*h+2 = n*2 by omega, pow_mul, hζ.pow_eq_one, one_pow]
  have he : (ζ^4)^h = (ζ^2)⁻¹ := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hz))
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hz)]
    exact hmul
  refine ⟨he, ?_⟩
  rw [pow_succ, he]
  field_simp

/- The reciprocal deformation is regular at u=1 for all its reversed factors. -/
omit [CharZero K] in
lemma shift_factors_at_one (_hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (h : ℕ) (hh : h < n) :
    (∀ j < h, 1-ζ^((h:ℤ)-(j:ℤ)) ≠ 0) ∧
    (∀ j < h, 1-ζ^(-1-(j:ℤ)) ≠ 0) := by
  constructor
  · intro j hj
    have hd : (h:ℤ)-(j:ℤ) = ((h-j:ℕ):ℤ) := by omega
    rw [hd, zpow_natCast]
    apply one_sub_root_pow_ne_zero hζ
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  · intro j hj
    have hd : -1-(j:ℤ) = -((j+1:ℕ):ℤ) := by omega
    rw [hd, zpow_neg, zpow_natCast]
    apply sub_ne_zero.mpr
    intro he
    have he' : ζ^(j+1) = 1 := by
      have := congrArg (Inv.inv : K → K) he
      simpa using this.symm
    exact (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)) he'


end
#print axioms cyclotomic_square_dvd_of_aeval_zero
#print axioms binomial_coprime_cyclotomic
#print axioms plus_binomial_coprime_cyclotomic
end Guo62
```

### `GuoCongSqAlgebra.lean`

```lean
import GuoCongruence

namespace Guo62
open Polynomial
noncomputable section

lemma CongSq.refl (n : ℕ) {f : RatFunc ℚ} (hf : Regular (cyclotomic n ℚ) f) :
    CongSq n f f := by
  exact ⟨hf,hf,by simp⟩

lemma CongSq.symm {n : ℕ} {f g : RatFunc ℚ} (h : CongSq n f g) : CongSq n g f := by
  refine ⟨h.2.1,h.1,?_⟩
  have hd := pow_dvd_num_mul 2 (Regular.sub h.1 h.2.1)
    (Regular.poly _ (-1)) h.2.2
  convert hd using 1
  congr 1
  simp


lemma CongSq.add {n : ℕ} {f g a b : RatFunc ℚ}
    (h : CongSq n f g) (h' : CongSq n a b) : CongSq n (f+a) (g+b) := by
  refine ⟨Regular.add h.1 h'.1, Regular.add h.2.1 h'.2.1, ?_⟩
  have hd := pow_dvd_num_add 2 (Regular.sub h.1 h.2.1)
    (Regular.sub h'.1 h'.2.1) h.2.2 h'.2.2
  convert hd using 1
  congr 1
  ring

lemma CongSq.trans {n : ℕ} {f g k : RatFunc ℚ}
    (h : CongSq n f g) (h' : CongSq n g k) : CongSq n f k := by
  refine ⟨h.1,h'.2.1,?_⟩
  have hd := pow_dvd_num_add 2 (Regular.sub h.1 h.2.1)
    (Regular.sub h'.1 h'.2.1) h.2.2 h'.2.2
  simpa only [sub_add_sub_cancel] using hd

lemma CongSq.mul {n : ℕ} {f g a b : RatFunc ℚ}
    (h : CongSq n f g) (h' : CongSq n a b) : CongSq n (f*a) (g*b) := by
  refine ⟨Regular.mul h.1 h'.1, Regular.mul h.2.1 h'.2.1, ?_⟩
  have hd1 := pow_dvd_num_mul 2 (Regular.sub h.1 h.2.1) h'.1 h.2.2
  have hd2 := pow_dvd_num_mul 2 (Regular.sub h'.1 h'.2.1) h.2.1 h'.2.2
  have hd := pow_dvd_num_add 2 ((Regular.sub h.1 h.2.1).mul h'.1)
    ((Regular.sub h'.1 h'.2.1).mul h.2.1) hd1 hd2
  convert hd using 1
  congr 1
  ring

lemma CongSq.sum {ι : Type*} (s : Finset ι) {n : ℕ} (f g : ι → RatFunc ℚ)
    (h : ∀ i ∈ s, CongSq n (f i) (g i)) : CongSq n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CongSq.refl n (Regular.zero _)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma Regular.const (p : ℚ[X]) (c : ℚ) : Regular p (algebraMap ℚ (RatFunc ℚ) c) := by
  simpa [embed] using Regular.poly p (C c)

end
end Guo62
```

### `GuoDixonProducts.lean`

```lean
import GuoProducts
import GuoAlgebra

namespace Guo62
noncomputable section
section
variable {K : Type*} [Field K]

def paramPoch (a Q : K) (k : ℕ) : K := ∏ j ∈ Finset.range k, (1-a*Q^j)

lemma paramPoch_succ (a Q : K) (k : ℕ) :
    paramPoch a Q (k+1) = paramPoch a Q k * (1-a*Q^k) :=
  Finset.prod_range_succ _ _

lemma paramPoch_shift (a Q : K) (k : ℕ) :
    paramPoch (a*Q) Q k * (1-a) = paramPoch a Q k * (1-a*Q^k) := by
  induction k with
  | zero => simp [paramPoch]
  | succ k ih =>
    rw [paramPoch_succ, paramPoch_succ, pow_succ]
    calc
      _ = (paramPoch (a*Q) Q k * (1-a)) * (1-a*(Q^k*Q)) := by ring
      _ = _ := by rw [ih]

/-- The Dixon term with the terminating parameter W, separated from indexing. -/
def dixonTerm {K : Type*} [Field K] (q W : K) (k : ℕ) : K :=
  (1+q^(4*k+1))/(1+q) * q^k *
    (paramPoch (q^2) (q^4) k * paramPoch W⁻¹ (q^4) k *
      paramPoch (q^4*W) (q^4) k) /
    (paramPoch (q^4) (q^4) k * paramPoch (q^2/W) (q^4) k *
      paramPoch (q^6*W) (q^4) k)

def dixonR {K : Type*} [Field K] (q W X : K) : K :=
  (1+W)/(q*W-1) * (1-X)*(1-q^2*W*X) / ((1+q*X)*(1-W*X))

def dixonV {K : Type*} [Field K] (q W X : K) : K :=
  (q-W)/(1-q*W) * (W-X)*(1-q^2*W*X) / ((1-W*X)*(W-q^2*X))

def dixonT {K : Type*} [Field K] (q W X : K) : K :=
  q*(1+q^5*X)/(1+q*X) *
    ((1-q^2*X)*(W-X)*(1-q^4*W*X)) /
    ((1-q^4*X)*(W-q^2*X)*(1-q^6*W*X))

lemma dixon_certificate {K : Type*} [Field K] (q W X : K)
    (h1 : q*W-1≠0) (h2 : 1+q*X≠0) (h3 : 1-W*X≠0)
    (h4 : W-q^2*X≠0) (h5 : 1+q^5*X≠0)
    (h6 : 1-q^4*X≠0) (h7 : 1-q^6*W*X≠0) (h8 : 1-q^4*W*X≠0) :
    dixonT q W X * dixonR q W (q^4*X) - dixonR q W X = 1-dixonV q W X := by
  have h1' : 1-q*W≠0 := by exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h1))
  dsimp [dixonT, dixonR, dixonV]
  have h5' : 1+q*(q^4*X)≠0 := by convert h5 using 1; ring
  have h7' : 1-q^2*W*(q^4*X)=1-q^6*W*X := by ring
  have h8' : 1-W*(q^4*X)≠0 := by convert h8 using 1; ring
  have h3c : 1-X*W≠0 := by simpa only [mul_comm] using h3
  have h7c : 1-q^6*X*W≠0 := by convert h7 using 1; ring
  have h8c : 1-q^4*X*W≠0 := by convert h8 using 1; ring
  rw [h7']
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [h1, h1', h2, h3, h4, h5, h5', h6, h7, h8, h8', h3c, h7c, h8c]
 ; ring

end
end
end Guo62
```

### `GuoGeometric.lean`

```lean
import Mathlib.Tactic.LinearCombination
import GuoCongruence
import GuoProducts
import GuoRoots
import Mathlib.Algebra.BigOperators.Intervals

/-! Geometric representatives remove a genuine common zero before root
substitution. This is the local ingredient for matched factors in full blocks. -/
namespace Guo62
open Polynomial
noncomputable section

def geomPoly (n a : ℕ) : ℚ[X] := ∑ j ∈ Finset.range a, X^(n*j)

lemma geomPoly_map (n a : ℕ) :
    embed (geomPoly n a) = ∑ j ∈ Finset.range a, q^(n*j) := by
  simp [embed, geomPoly, RatFunc.algebraMap_X]

lemma geomPoly_eval_one (n a : ℕ) : (geomPoly n a).eval 1 = a := by
  simp [geomPoly, eval_finsetSum]

lemma geomPoly_ne_zero (n : ℕ) {a : ℕ} (ha : 0 < a) : geomPoly n a ≠ 0 := by
  intro hz
  have hh := congrArg (fun P : ℚ[X] => P.eval 1) hz
  rw [geomPoly_eval_one, eval_zero] at hh
  exact (Nat.cast_ne_zero.mpr ha.ne') hh

/-- An actual identity in ℚ(q); the vanishing factor 1-q^n is cancelled
symbolically, before passing to a primitive root. -/
theorem matched_factor_cancel (n a b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    (1-q^(n*a))/(1-q^(n*b)) = embed (geomPoly n a) / embed (geomPoly n b) := by
  rw [geomPoly_map, geomPoly_map]
  simp_rw [pow_mul]
  exact geometric_cancel (q^n) a b
    (Ne.symm (sub_ne_zero.mp (one_sub_q_pow_ne_zero hn)))
    (by simp_rw [← pow_mul]; rw [← geomPoly_map]; exact RatFunc.algebraMap_ne_zero (geomPoly_ne_zero n hb))

section Roots
variable {K : Type*} [Field K] [CharZero K] {ζ : K}

lemma geomPoly_aeval_of_pow_eq_one (n a : ℕ) (hz : ζ^n = 1) :
    aeval ζ (geomPoly n a) = (a : K) := by
  simp [geomPoly, pow_mul, hz]

lemma euler_X_pow (k : ℕ) :
    (X : ℚ[X]) * (X^k).derivative = C (k:ℚ) * X^k := by
  cases k with
  | zero => simp
  | succ k => simp only [derivative_X_pow, Nat.add_sub_cancel]; ring

/-- Twice the Euler derivative of a cancelled geometric factor at a root.
This division-free formula includes the empty product a=0. -/
theorem geomPoly_euler_at_root (n a : ℕ) (hz : ζ^n = 1) :
    2 * (ζ * aeval ζ (geomPoly n a).derivative) =
      (n:K) * (a:K) * ((a:K)-1) := by
  have he : X * (geomPoly n a).derivative =
      ∑ j ∈ Finset.range a, C ((n*j:ℕ):ℚ) * X^(n*j) := by
    simp only [geomPoly, derivative_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact euler_X_pow _
  have hv := congrArg (aeval ζ) he
  simp only [map_mul, aeval_X, map_sum, map_pow, pow_mul, hz, one_pow,
    mul_one, Nat.cast_mul, map_natCast] at hv
  rw [hv, ← Finset.mul_sum]
  have ha : 2 * (∑ j ∈ Finset.range a, (j:K)) = (a:K)*((a:K)-1) := by
    cases a with
    | zero => simp
    | succ a =>
      have hs := Finset.sum_range_id_mul_two (a+1)
      have hc := congrArg (Nat.cast : ℕ → K) hs
      push_cast at hc
      simpa [mul_comm] using hc
  calc
    2 * ((n:K) * ∑ j ∈ Finset.range a, (j:K)) =
      (n:K) * (2 * ∑ j ∈ Finset.range a, (j:K)) := by ring
    _ = _ := by rw [ha]; ring

/-- The cancelled geometric denominator really is a unit modulo Φ_n. -/
lemma geomPoly_coprime_cyclotomic {n b : ℕ} (hn : 0 < n) (hb : 0 < b)
    (hζ : IsPrimitiveRoot ζ n) : IsCoprime (cyclotomic n ℚ) (geomPoly n b) := by
  apply coprime_cyclotomic_of_aeval_ne_zero hn hζ
  rw [geomPoly_aeval_of_pow_eq_one n b hζ.pow_eq_one]
  exact Nat.cast_ne_zero.mpr hb.ne'

/-- The actual cancelled rational factor is regular, not merely assigned a
value by a totalized division convention. -/
theorem matched_factor_regular {n a b : ℕ} (hn : 0 < n) (hb : 0 < b)
    (hζ : IsPrimitiveRoot ζ n) :
    Regular (cyclotomic n ℚ) ((1-q^(n*a))/(1-q^(n*b))) := by
  rw [matched_factor_cancel n a b hn hb]
  exact regular_of_fraction (geomPoly_ne_zero n hb) (geomPoly_coprime_cyclotomic hn hb hζ)

/-- Exact logarithmic Euler derivative of a matched zero-factor quotient.
Both values divided by are the nonzero integers a and b. -/
theorem matched_factor_log_derivative (n a b : ℕ) (hz : ζ^n = 1)
    (ha : 0 < a) (hb : 0 < b) :
    ζ * (aeval ζ (geomPoly n a).derivative / (a:K) -
      aeval ζ (geomPoly n b).derivative / (b:K)) =
        (n:K)*((a:K)-(b:K))/2 := by
  have ha0 : (a:K) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb0 : (b:K) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hda : ζ * aeval ζ (geomPoly n a).derivative = (n:K)*(a:K)*((a:K)-1)/2 := by
    apply (eq_div_iff (by norm_num : (2:K) ≠ 0)).mpr
    linear_combination geomPoly_euler_at_root n a hz
  have hdb : ζ * aeval ζ (geomPoly n b).derivative = (n:K)*(b:K)*((b:K)-1)/2 := by
    apply (eq_div_iff (by norm_num : (2:K) ≠ 0)).mpr
    linear_combination geomPoly_euler_at_root n b hz
  calc
    _ = (ζ * aeval ζ (geomPoly n a).derivative) / (a:K) -
        (ζ * aeval ζ (geomPoly n b).derivative) / (b:K) := by ring
    _ = _ := by rw [hda, hdb]; field_simp; ring


end Roots
end
#print axioms matched_factor_cancel
#print axioms geomPoly_euler_at_root
#print axioms matched_factor_regular
#print axioms matched_factor_log_derivative
#print axioms geomPoly_coprime_cyclotomic
end Guo62
```

### `GuoAudit.lean`

```lean
import GuoAlgebra
import GuoStatement
import GuoCongruence
import GuoProducts
import GuoRoots
import GuoReciprocity
import GuoGeometric
import GuoFirstOrder

/-! Full declaration and axiom inventory for this partial packet. -/
#eval Lean.versionString
#print Guo62.GuoConjecture62
#print Guo62.lhs
#print Guo62.rhs
#check GuoBlockLift.weighted_involution_average
#print axioms GuoBlockLift.weighted_involution_average
#check GuoBlockLift.core_constant_cancels
#print axioms GuoBlockLift.core_constant_cancels
#check GuoBlockLift.block_error_sum_zero
#print axioms GuoBlockLift.block_error_sum_zero
#check GuoBlockLift.finite_dixon_certificate
#print axioms GuoBlockLift.finite_dixon_certificate
#check GuoBlockLift.square_dvd_of_dvd_derivative
#print axioms GuoBlockLift.square_dvd_of_dvd_derivative
#check Guo62.pochPoly_map
#print axioms Guo62.pochPoly_map
#check Guo62.one_sub_X_pow_ne_zero
#print axioms Guo62.one_sub_X_pow_ne_zero
#check Guo62.one_add_X_pow_ne_zero
#print axioms Guo62.one_add_X_pow_ne_zero
#check Guo62.one_sub_q_pow_ne_zero
#print axioms Guo62.one_sub_q_pow_ne_zero
#check Guo62.one_add_q_pow_ne_zero
#print axioms Guo62.one_add_q_pow_ne_zero
#check Guo62.one_add_q_ne_zero
#print axioms Guo62.one_add_q_ne_zero
#check Guo62.q_pow_ne_zero
#print axioms Guo62.q_pow_ne_zero
#check Guo62.poch_ne_zero
#print axioms Guo62.poch_ne_zero
#check Guo62.lhs_denominator_ne_zero
#print axioms Guo62.lhs_denominator_ne_zero
#check Guo62.rhs_poch_denominator_ne_zero
#print axioms Guo62.rhs_poch_denominator_ne_zero
#check Guo62.factorial_denominator_ne_zero
#print axioms Guo62.factorial_denominator_ne_zero
#check Guo62.endpoint_denominators_nonzero
#print axioms Guo62.endpoint_denominators_nonzero
#check Guo62.halfPoch_pos
#print axioms Guo62.halfPoch_pos
#check Guo62.admissible_half
#print axioms Guo62.admissible_half
#check Guo62.regular_of_fraction
#print axioms Guo62.regular_of_fraction
#check Guo62.regular_iff_fraction
#print axioms Guo62.regular_iff_fraction
#check Guo62.pow_dvd_num_fraction_iff
#print axioms Guo62.pow_dvd_num_fraction_iff
#check Guo62.sub_fractions
#print axioms Guo62.sub_fractions
#check Guo62.congSq_fractions_iff
#print axioms Guo62.congSq_fractions_iff
#check Guo62.Regular.zero
#print axioms Guo62.Regular.zero
#check Guo62.Regular.one
#print axioms Guo62.Regular.one
#check Guo62.Regular.poly
#print axioms Guo62.Regular.poly
#check Guo62.Regular.add
#print axioms Guo62.Regular.add
#check Guo62.Regular.mul
#print axioms Guo62.Regular.mul
#check Guo62.Regular.neg
#print axioms Guo62.Regular.neg
#check Guo62.Regular.sub
#print axioms Guo62.Regular.sub
#check Guo62.Regular.sum
#print axioms Guo62.Regular.sum
#check Guo62.pow_dvd_num_add
#print axioms Guo62.pow_dvd_num_add
#check Guo62.pow_dvd_num_mul
#print axioms Guo62.pow_dvd_num_mul
#check Guo62.qInt2_eq_fraction
#print axioms Guo62.qInt2_eq_fraction
#check Guo62.geometric_cancel
#print axioms Guo62.geometric_cancel
#check Guo62.poch_add
#print axioms Guo62.poch_add
#check Guo62.halfPoch_succ
#print axioms Guo62.halfPoch_succ
#check Guo62.half_ratio_step
#print axioms Guo62.half_ratio_step
#check Guo62.cyclotomic_dvd_iff_aeval_zero
#print axioms Guo62.cyclotomic_dvd_iff_aeval_zero
#check Guo62.cyclotomic_square_dvd_of_aeval_zero
#print axioms Guo62.cyclotomic_square_dvd_of_aeval_zero
#check Guo62.coprime_cyclotomic_of_aeval_ne_zero
#print axioms Guo62.coprime_cyclotomic_of_aeval_ne_zero
#check Guo62.one_sub_root_pow_ne_zero
#print axioms Guo62.one_sub_root_pow_ne_zero
#check Guo62.binomial_coprime_cyclotomic
#print axioms Guo62.binomial_coprime_cyclotomic
#check Guo62.one_add_root_pow_ne_zero
#print axioms Guo62.one_add_root_pow_ne_zero
#check Guo62.plus_binomial_coprime_cyclotomic
#print axioms Guo62.plus_binomial_coprime_cyclotomic
#check Guo62.fourth_power_primitive
#print axioms Guo62.fourth_power_primitive
#check Guo62.root_half_relations
#print axioms Guo62.root_half_relations
#check Guo62.shift_factors_at_one
#print axioms Guo62.shift_factors_at_one
#check Guo62.prefixProd_complement
#print axioms Guo62.prefixProd_complement
#check Guo62.reciprocal_pair
#print axioms Guo62.reciprocal_pair
#check Guo62.shiftRatio_reflection
#print axioms Guo62.shiftRatio_reflection
#check Guo62.shiftTerm_reflection
#print axioms Guo62.shiftTerm_reflection
#check Guo62.shiftSum_reciprocity
#print axioms Guo62.shiftSum_reciprocity
#check Guo62.geomPoly_map
#print axioms Guo62.geomPoly_map
#check Guo62.geomPoly_eval_one
#print axioms Guo62.geomPoly_eval_one
#check Guo62.geomPoly_ne_zero
#print axioms Guo62.geomPoly_ne_zero
#check Guo62.matched_factor_cancel
#print axioms Guo62.matched_factor_cancel
#check Guo62.geomPoly_aeval_of_pow_eq_one
#print axioms Guo62.geomPoly_aeval_of_pow_eq_one
#check Guo62.euler_X_pow
#print axioms Guo62.euler_X_pow
#check Guo62.geomPoly_euler_at_root
#print axioms Guo62.geomPoly_euler_at_root
#check Guo62.geomPoly_coprime_cyclotomic
#print axioms Guo62.geomPoly_coprime_cyclotomic
#check Guo62.matched_factor_regular
#print axioms Guo62.matched_factor_regular
#check Guo62.matched_factor_log_derivative
#print axioms Guo62.matched_factor_log_derivative
#check Guo62.half_block_error_zero
#print axioms Guo62.half_block_error_zero
#check Guo62.first_order_block_assembly
#print axioms Guo62.first_order_block_assembly
```

### `GuoBlockIndex.lean`

```lean
import GuoGeometric

/-! Explicit indexing of a cancelled n-term block. The low numerator factors
are paired with upper denominator residues; the high numerator factors are
paired with lower denominator residues. -/
namespace Guo62
open Polynomial
noncomputable section

def blockNum (n h u : ℕ) : ℚ[X] :=
  geomPoly n (4*u+2) * pochPoly (4*(u*n)+2) 4 h *
    pochPoly (4*(u*n)+4*h+6) 4 h

def blockDen (n h u : ℕ) : ℚ[X] :=
  geomPoly n (4*u+4) * pochPoly (4*(u*n)+4*h+4) 4 h *
    pochPoly (4*(u*n)+4) 4 h

lemma poch_one (a d : ℕ) : poch a d 1 = 1-q^a := by simp [poch]

lemma poch_split_middle (a h : ℕ) :
    poch a 4 (2*h+1) = poch a 4 h * (1-q^(a+4*h)) * poch (a+4*h+4) 4 h := by
  rw [show 2*h+1 = h+(1+h) by omega, poch_add a 4 h (1+h),
    poch_add (a+4*h) 4 1 h, poch_one]
  simp only [Nat.mul_one]
  ring

lemma poch_split_last (a h : ℕ) :
    poch a 4 (2*h+1) = poch a 4 h * poch (a+4*h) 4 h * (1-q^(a+8*h)) := by
  rw [show 2*h+1 = (h+h)+1 by omega, poch_add a 4 (h+h) 1,
    poch_add a 4 h h, poch_one]
  rw [show a+4*(h+h)=a+8*h by omega]

/-- Faithful cancellation in the actual rational-function block, with no
root evaluation of the raw singular denominator. -/
theorem block_fraction_identity (n h u : ℕ) (hn : 0<n) (hh : n=2*h+1) :
    poch (4*(u*n)+2) 4 n / poch (4*(u*n)+4) 4 n =
      embed (blockNum n h u) / embed (blockDen n h u) := by
  have hna : 4*(u*n)+2+4*h = n*(4*u+2) := by rw [hh]; ring
  have hnb : 4*(u*n)+4+8*h = n*(4*u+4) := by rw [hh]; ring
  rw [hh, poch_split_middle, poch_split_last]
  rw [← hh, hna, hnb]
  have hm := matched_factor_cancel n (4*u+2) (4*u+4) hn (by omega)
  simp only [blockNum, blockDen, map_mul, show embed = algebraMap ℚ[X] (RatFunc ℚ) from rfl,
    pochPoly_map]
  rw [show n*(4*u+2)+4 = 4*(u*n)+4*h+6 by omega,
    show 4*(u*n)+4+4*h = 4*(u*n)+4*h+4 by omega]
  calc
    _ = ((1-q^(n*(4*u+2)))/(1-q^(n*(4*u+4)))) *
        (poch (4*(u*n)+2) 4 h * poch (4*(u*n)+4*h+6) 4 h /
        (poch (4*(u*n)+4*h+4) 4 h * poch (4*(u*n)+4) 4 h)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hm]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

section Roots
variable {K : Type*} [Field K] {z : K}

lemma block_pow (n u a : ℕ) (hz : z^n=1) : z^(4*(u*n)+a) = z^a := by
  rw [pow_add, show 4*(u*n)=n*(4*u) by ring, pow_mul, hz, one_pow, one_mul]

/-- First residue permutation, including its exact exponent difference. -/
lemma low_residue (n h u j : ℕ) (hh : n=2*h+1) (hz : z^n=1) :
    z^(4*(u*n)+2+4*j) = z^(4*(h+1+j)) := by
  rw [show 4*(u*n)+2+4*j = 4*(u*n)+(4*j+2) by omega, block_pow n u _ hz]
  have he : 4*(h+1+j) = (4*j+2)+n*2 := by rw [hh]; ring
  conv_rhs => rw [he, pow_add, pow_mul z n, hz, one_pow, mul_one]

/-- Second residue permutation. -/
lemma high_residue (n h u j : ℕ) (hh : n=2*h+1) (hz : z^n=1) :
    z^(4*(u*n)+4*h+6+4*j) = z^(4*(j+1)) := by
  have he : 4*(u*n)+4*h+6+4*j = 4*(j+1)+n*(4*u+2) := by rw [hh]; ring
  conv_lhs => rw [he, pow_add, pow_mul z n, hz, one_pow, mul_one]

lemma denominator_residue_low (n u j : ℕ) (hz : z^n=1) :
    z^(4*(u*n)+4+4*j) = z^(4*(j+1)) := by
  rw [show 4*(u*n)+4+4*j=4*(u*n)+4*(j+1) by ring, block_pow n u _ hz]

lemma denominator_residue_high (n h u j : ℕ) (hz : z^n=1) :
    z^(4*(u*n)+4*h+4+4*j) = z^(4*(h+1+j)) := by
  rw [show 4*(u*n)+4*h+4+4*j=4*(u*n)+4*(h+1+j) by ring, block_pow n u _ hz]

/-- All nonzero residue factors really are units; n need only be odd. -/
lemma block_residue_units (n h : ℕ) (hh : n=2*h+1) (hz : IsPrimitiveRoot z n) :
    (∀ j<h, 1-z^(4*(j+1)) ≠ 0) ∧ (∀ j<h, 1-z^(4*(h+1+j)) ≠ 0) := by
  have ho : Odd n := ⟨h, by omega⟩
  have hQ := fourth_power_primitive ho hz
  constructor
  · intro j hj
    simpa only [pow_mul] using one_sub_root_pow_ne_zero hQ
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : j+1<n))
  · intro j hj
    simpa only [pow_mul] using one_sub_root_pow_ne_zero hQ
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : h+1+j<n))

variable [CharZero K]

lemma pochPoly_aeval (a d k : ℕ) :
    aeval z (pochPoly a d k) = ∏ j ∈ Finset.range k, (1-z^(a+d*j)) := by
  simp [pochPoly]

lemma blockDen_aeval_ne_zero (n h u : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) : aeval z (blockDen n h u) ≠ 0 := by
  obtain ⟨hl, hr⟩ := block_residue_units n h hh hz
  simp only [blockDen, map_mul, geomPoly_aeval_of_pow_eq_one n _ hz.pow_eq_one,
    pochPoly_aeval]
  refine mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ?_) ?_
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [denominator_residue_high n h u j hz.pow_eq_one]
    exact hr j (Finset.mem_range.mp hj)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [denominator_residue_low n u j hz.pow_eq_one]
    exact hl j (Finset.mem_range.mp hj)

lemma blockNum_aeval_ne_zero (n h u : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) : aeval z (blockNum n h u) ≠ 0 := by
  obtain ⟨hl, hr⟩ := block_residue_units n h hh hz
  simp only [blockNum, map_mul, geomPoly_aeval_of_pow_eq_one n _ hz.pow_eq_one,
    pochPoly_aeval]
  refine mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ?_) ?_
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [low_residue n h u j hh hz.pow_eq_one]
    exact hr j (Finset.mem_range.mp hj)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [high_residue n h u j hh hz.pow_eq_one]
    exact hl j (Finset.mem_range.mp hj)

lemma block_fraction_regular (n h u : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    Regular (cyclotomic n ℚ) (poch (4*(u*n)+2) 4 n / poch (4*(u*n)+4) 4 n) := by
  rw [block_fraction_identity n h u hn hh]
  have hb := blockDen_aeval_ne_zero n h u hh hz
  apply regular_of_fraction
  · intro he; exact hb (by rw [he, map_zero])
  · exact coprime_cyclotomic_of_aeval_ne_zero hn hz _ hb

end Roots
end
end Guo62
```

### `GuoDixonRecurrence.lean`

```lean
import GuoDixonProducts

namespace Guo62
noncomputable section
section
variable {K : Type*} [Field K]

lemma paramPoch_shift_div (a Q : K) (k : ℕ) (ha : 1-a≠0) :
    paramPoch (a*Q) Q k = paramPoch a Q k * (1-a*Q^k)/(1-a) := by
  exact (eq_div_iff ha).mpr (paramPoch_shift a Q k)

lemma paramPoch_unshift_div (a Q : K) (k : ℕ) (ha : 1-a*Q^k≠0) :
    paramPoch a Q k = paramPoch (a*Q) Q k * (1-a)/(1-a*Q^k) := by
  exact (eq_div_iff ha).mpr (paramPoch_shift a Q k).symm

def dixonRate (q W : K) : K :=
  q⁻¹ * (1-q^2*W)/(1-W/q^2) * (1-W/q)/(1-q*W)

lemma dixon_parameter_step (q W : K) (k : ℕ) (hq : q≠0) (hW : W≠0)
    (h1 : 1-W⁻¹≠0) (h2 : 1-W*q^(4*k)≠0)
    (h3 : 1-q^2/W≠0) (h4 : 1-q^2*W*q^(4*k)≠0)
    (h5 : 1-q^2*W≠0) (_h6 : 1-W/q^2≠0) (h7 : 1-q*W≠0)
    (h8 : W-q^2*q^(4*k)≠0)
    (hplus : 1+q≠0) (hQ : paramPoch (q^4) (q^4) k≠0)
    (hW1 : W-1≠0) (hW2 : W-q^2≠0)
    (hP : paramPoch (q^2/W) (q^4) k≠0)
    (hS : paramPoch (q^6*W) (q^4) k≠0) :
    dixonRate q W * dixonTerm q (W/q^4) k =
      dixonTerm q W k * dixonV q W (q^(4*k)) := by
  have hp1 := paramPoch_shift_div W⁻¹ (q^4) k h1
  have hp2 := paramPoch_unshift_div W (q^4) k (by simpa only [← pow_mul] using h2)
  have hp3 := paramPoch_shift_div (q^2/W) (q^4) k h3
  have hp4 := paramPoch_unshift_div (q^2*W) (q^4) k (by simpa only [← pow_mul] using h4)
  have hA : (W/q^4)⁻¹ = W⁻¹*q^4 := by field_simp
  have hB : q^4*(W/q^4)=W := by field_simp
  have hC : q^2/(W/q^4)=(q^2/W)*q^4 := by field_simp
  have hD : q^6*(W/q^4)=q^2*W := by field_simp
  have hE : W*q^4=q^4*W := mul_comm _ _
  have hG : q^2*W*q^4=q^6*W := by ring
  dsimp only [dixonTerm]
  rw [hA,hB,hC,hD,hp1,hp2,hp3,hp4,hE,hG]
  simp only [← pow_mul]
  generalize hX : q^(4*k)=X at *
  dsimp only [dixonRate,dixonV]
  have h2c : 1-X*W≠0 := by simpa only [mul_comm] using h2
  have h4c : 1-q^2*X*W≠0 := by convert h4 using 1; ring
  have h5c : q^2-W≠0 := by exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hW2))
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp [hq,hW,h1,h2,h3,h4,h5,_h6,h7,h8,hP,hS,hQ,hplus,hW1,hW2,h2c,h4c,h5c]
  ring

end
end
end Guo62
```

### `GuoDixonTermStep.lean`

```lean
import GuoDixonProducts

namespace Guo62
noncomputable section
section
variable {K : Type*} [Field K]

lemma dixon_term_step (q W : K) (k : ℕ) (hW : W≠0)
    (h1 : 1+q≠0) (h2 : 1+q*q^(4*k)≠0) (h3 : 1-q^4*q^(4*k)≠0)
    (h4 : W-q^2*q^(4*k)≠0) (h5 : 1-q^6*W*q^(4*k)≠0)
    (hQ : paramPoch (q^4) (q^4) k≠0)
    (hP : paramPoch (q^2/W) (q^4) k≠0)
    (hS : paramPoch (q^6*W) (q^4) k≠0) :
    dixonTerm q W (k+1) = dixonTerm q W k * dixonT q W (q^(4*k)) := by
  have he1 : q^(4*(k+1)+1)=q^5*q^(4*k) := by rw [← pow_add]; congr 1; omega
  have he2 : q^(4*k+1)=q*q^(4*k) := by rw [pow_succ']
  dsimp only [dixonTerm]
  rw [he1,he2,pow_succ]
  simp only [paramPoch_succ, ← pow_mul]
  dsimp only [dixonT]
  generalize hX : q^(4*k)=X at *
  have h5c : 1-q^6*X*W≠0 := by convert h5 using 1; ring
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [hW,h1,h2,h3,h4,h5,h5c,hQ,hP,hS]
  ring

end
end
end Guo62
```

### `GuoDixonUnits.lean`

```lean
import GuoDixonProducts

namespace Guo62
open Polynomial
noncomputable section

lemma q_pow_injective : Function.Injective (fun k : ℕ => q^k) := by
  intro a b h
  have hp : (X^a : ℚ[X]) = X^b := by
    apply (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
    simpa only [map_pow, RatFunc.algebraMap_X] using h
  have := congrArg Polynomial.natDegree hp
  simpa using this

lemma q_zpow_ne_one (a : ℤ) (ha : a≠0) : q^a≠1 := by
  cases a with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    intro he
    have := q_pow_injective (he.trans (pow_zero q).symm)
    exact ha (by simpa using this)
  | negSucc a =>
    rw [zpow_negSucc]
    intro he
    have hp : q^(a+1)=1 := inv_eq_one.mp he
    have := q_pow_injective (hp.trans (pow_zero q).symm)
    omega

lemma one_sub_q_zpow_ne_zero (a : ℤ) (ha : a≠0) : 1-q^a≠0 :=
  sub_ne_zero.mpr (Ne.symm (q_zpow_ne_one a ha))

def pochZ (a d : ℤ) (k : ℕ) : RatFunc ℚ :=
  ∏ j ∈ Finset.range k, (1-q^(a+d*(j:ℤ)))

lemma pochZ_param (a : ℤ) (k : ℕ) : pochZ a 4 k = paramPoch (q^a) (q^4) k := by
  unfold pochZ paramPoch
  apply Finset.prod_congr rfl
  intro j _
  rw [zpow_add₀ RatFunc.X_ne_zero, zpow_mul, zpow_ofNat, zpow_natCast]

lemma pochZ_nat (a d k : ℕ) : pochZ a d k = poch a d k := by
  simp only [pochZ, poch, ← Nat.cast_mul, ← Nat.cast_add, zpow_natCast]

lemma pochZ_ne_zero (a d : ℤ) (k : ℕ) (h : ∀ j<k, a+d*(j:ℤ)≠0) :
    pochZ a d k≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact one_sub_q_zpow_ne_zero _ (h j (Finset.mem_range.mp hj))

def terminatingTerm (N k : ℕ) : RatFunc ℚ :=
  ((1+q^(4*k+1))/(1+q))*q^k *
  (pochZ 2 4 k * pochZ (-4*(N:ℤ)) 4 k * pochZ (4*(N:ℤ)+4) 4 k) /
  (pochZ 4 4 k * pochZ (2-4*(N:ℤ)) 4 k * pochZ (4*(N:ℤ)+6) 4 k)

lemma terminating_denominators (N k : ℕ) :
    pochZ 4 4 k≠0 ∧ pochZ (2-4*(N:ℤ)) 4 k≠0 ∧ pochZ (4*(N:ℤ)+6) 4 k≠0 := by
  exact ⟨pochZ_ne_zero _ _ _ (by intro j hj; omega),
    pochZ_ne_zero _ _ _ (by intro j hj; omega),
    pochZ_ne_zero _ _ _ (by intro j hj; omega)⟩

lemma terminatingTerm_dixon (N k : ℕ) : terminatingTerm N k = dixonTerm q (q^(4*N)) k := by
  have h1 : q^(-4*(N:ℤ))=(q^(4*N))⁻¹ := by
    rw [show -4*(N:ℤ)=-((4*N:ℕ):ℤ) by omega,zpow_neg,zpow_natCast]
  have h2 : q^(4*(N:ℤ)+4)=q^4*q^(4*N) := by
    rw [show 4*(N:ℤ)+4=((4+4*N:ℕ):ℤ) by omega,zpow_natCast,pow_add]
  have h3 : q^(2-4*(N:ℤ))=q^2/q^(4*N) := by
    rw [show 2-4*(N:ℤ)=(2:ℤ)-((4*N:ℕ):ℤ) by omega,
      zpow_sub₀ (show q≠0 from RatFunc.X_ne_zero),zpow_ofNat,zpow_natCast]
  have h4 : q^(4*(N:ℤ)+6)=q^6*q^(4*N) := by
    rw [show 4*(N:ℤ)+6=((6+4*N:ℕ):ℤ) by omega,zpow_natCast,pow_add]
  simp only [terminatingTerm,dixonTerm,pochZ_param,h1,h2,h3,h4,zpow_ofNat]

lemma terminatingTerm_zero (N k : ℕ) (hk : N<k) : terminatingTerm N k=0 := by
  have hp : pochZ (-4*(N:ℤ)) 4 k=0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
    simp
  rw [terminatingTerm, hp]
  simp only [mul_zero, zero_mul, zero_div]

lemma terminatingTerm_at_zero (N : ℕ) : terminatingTerm N 0=1 := by
  simp [terminatingTerm, pochZ, one_add_q_ne_zero]

end
end Guo62
```

### `GuoLogDerivative.lean`

```lean
import GuoGeometric

/-! Finite-product logarithmic Euler derivatives of polynomial witnesses.
All divisions below require explicit nonzero evaluated factors in the lemmas
that use additivity. -/
namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def eulerLog (z : K) (P : ℚ[X]) : K := z * aeval z P.derivative / aeval z P

lemma eulerLog_one (z : K) : eulerLog z 1 = 0 := by simp [eulerLog]

lemma eulerLog_mul (z : K) (A B : ℚ[X])
    (hA : aeval z A ≠ 0) (hB : aeval z B ≠ 0) :
    eulerLog z (A*B) = eulerLog z A + eulerLog z B := by
  simp only [eulerLog, derivative_mul, map_add, map_mul]
  field_simp

/-- Induction over the factors, rather than expansion of the long product. -/
theorem eulerLog_prod {ι : Type*} (s : Finset ι) (z : K) (P : ι → ℚ[X])
    (hP : ∀ i ∈ s, aeval z (P i) ≠ 0) :
    eulerLog z (∏ i ∈ s, P i) = ∑ i ∈ s, eulerLog z (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eulerLog_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, eulerLog_mul]
    · rw [ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))]
    · exact hP i (Finset.mem_insert_self i s)
    · simp only [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun j hj => hP j (Finset.mem_insert_of_mem hj))

lemma eulerLog_binomial (z : K) (a : ℕ) :
    eulerLog z (1-X^a) = -(a:K) * (z^a/(1-z^a)) := by
  have he := congrArg (aeval z) (euler_X_pow a)
  simp only [map_mul, aeval_X, map_pow, aeval_C, eq_ratCast, Rat.cast_natCast] at he
  simp only [eulerLog, derivative_one, zero_sub, map_neg,
    map_sub, map_one, map_pow, aeval_X]
  rw [mul_neg, he]
  ring

lemma eulerLog_geom (z : K) (n a : ℕ) (hz : z^n=1) (ha : 0<a) :
    eulerLog z (geomPoly n a) = (n:K)*((a:K)-1)/2 := by
  rw [eulerLog, geomPoly_aeval_of_pow_eq_one n a hz]
  have he := geomPoly_euler_at_root n a hz
  have ha0 : (a:K) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  apply (div_eq_iff ha0).mpr
  linear_combination he / 2

/-- The quotient witness has the advertised derivative, expressed without
introducing a derivative on totalized RatFunc evaluation. -/
theorem quotient_euler_cross (z : K) (A B : ℚ[X])
    (hA : aeval z A ≠ 0) (hB : aeval z B ≠ 0) :
    z * (aeval z A.derivative * aeval z B - aeval z A * aeval z B.derivative) /
      (aeval z B)^2 = (aeval z A / aeval z B) * (eulerLog z A-eulerLog z B) := by
  unfold eulerLog
  field_simp

end
end Guo62
```

### `GuoHarmonic.lean`

```lean
import GuoBlockIndex

namespace Guo62
noncomputable section
variable {K : Type*} [Field K]

def rootFrac (x : K) : K := x/(1-x)

def halfHarmonic (z : K) (h : ℕ) : K :=
  ∑ j ∈ Finset.range h, rootFrac (z^(4*(j+1)))

lemma rootFrac_inv (x : K) (hx : x≠0) (h1 : 1-x≠0) :
    rootFrac x⁻¹ = -1-rootFrac x := by
  have hi : 1-x⁻¹ ≠ 0 := by
    intro he
    have hi : x⁻¹=1 := (sub_eq_zero.mp he).symm
    have := congrArg (Inv.inv : K → K) hi
    simp only [inv_inv, inv_one] at this
    exact h1 (by rw [this, sub_self])
  unfold rootFrac
  have hm : -1+x ≠ 0 := by intro h; exact h1 (by linear_combination -h)
  field_simp [hm]
  ring_nf
  field_simp [hm]
  ring

lemma upper_residue_inverse {z : K} (n h j : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) (hj : j<h) :
    z^(4*(h+1+j)) = (z^(4*(h-j)))⁻¹ := by
  have hn : n≠0 := by omega
  have he : 4*(h+1+j)+4*(h-j)=n*4 := by omega
  apply (mul_right_cancel₀ (pow_ne_zero (4*(h-j)) (hz.ne_zero hn)))
  rw [inv_mul_cancel₀ (pow_ne_zero _ (hz.ne_zero hn)), ← pow_add, he,
    pow_mul, hz.pow_eq_one, one_pow]

/-- The upper half of the nonzero residues is the inverted lower half.
This is the second, reversing permutation used in the core calculation. -/
theorem upper_harmonic (z : K) (n h : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    (∑ j ∈ Finset.range h, rootFrac (z^(4*(h+1+j)))) = -(h:K)-halfHarmonic z h := by
  have ho : Odd n := ⟨h, by omega⟩
  have hQ := fourth_power_primitive ho hz
  have ht : ∀ j<h, rootFrac (z^(4*(h+1+j))) = -1-rootFrac (z^(4*(h-j))) := by
    intro j hj
    rw [upper_residue_inverse n h j hh hz hj]
    apply rootFrac_inv
    · exact pow_ne_zero _ (hz.ne_zero (by omega))
    · simpa only [pow_mul] using one_sub_root_pow_ne_zero hQ
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : h-j<n))
  calc
    _ = ∑ j ∈ Finset.range h, (-1-rootFrac (z^(4*(h-j)))) :=
      Finset.sum_congr rfl (fun j hj => ht j (Finset.mem_range.mp hj))
    _ = -(h:K) - ∑ j ∈ Finset.range h, rootFrac (z^(4*(h-j))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ = _ := by
      congr 1
      rw [halfHarmonic, ← Finset.sum_range_reflect (fun j => rootFrac (z^(4*(j+1)))) h]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show h-1-j+1=h-j by have := Finset.mem_range.mp hj; omega]

end
end Guo62
```

### `GuoBlockDerivative.lean`

```lean
import GuoLogDerivative
import GuoHarmonic

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma eulerLog_pochPoly (a d k : ℕ) (hp : aeval z (pochPoly a d k) ≠ 0) :
    eulerLog z (pochPoly a d k) =
      ∑ j ∈ Finset.range k, -((a+d*j:ℕ):K)*rootFrac (z^(a+d*j)) := by
  rw [pochPoly_aeval] at hp
  unfold pochPoly
  rw [eulerLog_prod _ _ _ (by simpa using Finset.prod_ne_zero_iff.mp hp)]
  simp only [eulerLog_binomial, rootFrac]

lemma block_pair_values (n h u : ℕ) (hh : n=2*h+1) (hz : z^n=1) :
    aeval z (pochPoly (4*(u*n)+2) 4 h) =
      aeval z (pochPoly (4*(u*n)+4*h+4) 4 h) ∧
    aeval z (pochPoly (4*(u*n)+4*h+6) 4 h) =
      aeval z (pochPoly (4*(u*n)+4) 4 h) := by
  simp only [pochPoly_aeval]
  constructor
  · apply Finset.prod_congr rfl
    intro j _
    rw [low_residue n h u j hh hz, denominator_residue_high n h u j hz]
  · apply Finset.prod_congr rfl
    intro j _
    rw [high_residue n h u j hh hz, denominator_residue_low n u j hz]

/-- A whole cancelled block has the classical coefficient ratio as value. -/
theorem block_value (n h u : ℕ) (hh : n=2*h+1) (hz : IsPrimitiveRoot z n) :
    aeval z (blockNum n h u) / aeval z (blockDen n h u) =
      (2*(u:K)+1)/(2*(u:K)+2) := by
  obtain ⟨hp, hq⟩ := block_pair_values n h u hh hz.pow_eq_one
  have hDen := blockDen_aeval_ne_zero n h u hh hz
  simp only [blockDen, map_mul] at hDen
  obtain ⟨⟨_, hr⟩, hs⟩ := mul_ne_zero_iff.mp hDen |>.imp_left mul_ne_zero_iff.mp
  simp only [blockNum, blockDen, map_mul,
    geomPoly_aeval_of_pow_eq_one n _ hz.pow_eq_one, hp, hq]
  push_cast
  have hu : 2*(u:K)+2 ≠ 0 := by exact_mod_cast (show 2*u+2≠0 by omega)
  field_simp
  ring

/-- Uniform core calculation: the exponent shifts 4un cancel after the
explicit residue permutation. No hypothesis on u is needed. -/
theorem block_log_derivative (n h u : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    eulerLog z (blockNum n h u) - eulerLog z (blockDen n h u) =
      -(n:K)^2 - 4*(n:K)*halfHarmonic z h := by
  have hN := blockNum_aeval_ne_zero n h u hh hz
  have hD := blockDen_aeval_ne_zero n h u hh hz
  simp only [blockNum, map_mul, ne_eq, mul_eq_zero, not_or] at hN
  simp only [blockDen, map_mul, ne_eq, mul_eq_zero, not_or] at hD
  obtain ⟨⟨hNG, hNL⟩, hNH⟩ := hN
  obtain ⟨⟨hDG, hDH⟩, hDL⟩ := hD
  have hfirst : eulerLog z (pochPoly (4*(u*n)+2) 4 h) -
      eulerLog z (pochPoly (4*(u*n)+4*h+4) 4 h) =
      2*(n:K)*(∑ j ∈ Finset.range h, rootFrac (z^(4*(h+1+j)))) := by
    rw [eulerLog_pochPoly _ _ _ hNL, eulerLog_pochPoly _ _ _ hDH,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [low_residue n h u j hh hz.pow_eq_one,
      denominator_residue_high n h u j hz.pow_eq_one]
    have hc : (n:K) = 2*(h:K)+1 := by exact_mod_cast hh
    push_cast
    rw [hc]
    ring
  have hsecond : eulerLog z (pochPoly (4*(u*n)+4*h+6) 4 h) -
      eulerLog z (pochPoly (4*(u*n)+4) 4 h) =
      -2*(n:K)*halfHarmonic z h := by
    rw [eulerLog_pochPoly _ _ _ hNH, eulerLog_pochPoly _ _ _ hDL,
      ← Finset.sum_sub_distrib, halfHarmonic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [high_residue n h u j hh hz.pow_eq_one,
      denominator_residue_low n u j hz.pow_eq_one]
    have hc : (n:K) = 2*(h:K)+1 := by exact_mod_cast hh
    push_cast
    rw [hc]
    ring
  have hgeom : eulerLog z (geomPoly n (4*u+2)) - eulerLog z (geomPoly n (4*u+4)) = -(n:K) := by
    rw [eulerLog_geom z n _ hz.pow_eq_one (by omega),
      eulerLog_geom z n _ hz.pow_eq_one (by omega)]
    push_cast
    ring
  have hNum : eulerLog z (blockNum n h u) = eulerLog z (geomPoly n (4*u+2)) +
      eulerLog z (pochPoly (4*(u*n)+2) 4 h) + eulerLog z (pochPoly (4*(u*n)+4*h+6) 4 h) := by
    unfold blockNum
    rw [eulerLog_mul z _ _ (by simpa only [map_mul] using mul_ne_zero hNG hNL) hNH, eulerLog_mul z _ _ hNG hNL]
  have hDen : eulerLog z (blockDen n h u) = eulerLog z (geomPoly n (4*u+4)) +
      eulerLog z (pochPoly (4*(u*n)+4*h+4) 4 h) + eulerLog z (pochPoly (4*(u*n)+4) 4 h) := by
    unfold blockDen
    rw [eulerLog_mul z _ _ (by simpa only [map_mul] using mul_ne_zero hDG hDH) hDL, eulerLog_mul z _ _ hDG hDH]
  rw [hNum, hDen]
  have hUpper := upper_harmonic z n h hh hz
  have hc : (n:K) = 2*(h:K)+1 := by exact_mod_cast hh
  linear_combination hgeom + hfirst + hsecond + 2*(n:K)*hUpper +
    (n:K)*hc

end
end Guo62
```

### `GuoCore.lean`

```lean
import GuoBlockDerivative

/-! Polynomial witnesses for the complete R_(ln) core, with all l singular
pairs cancelled before primitive-root evaluation. -/
namespace Guo62
open Polynomial
noncomputable section

def coreNum (n h l : ℕ) : ℚ[X] := ∏ u ∈ Finset.range l, blockNum n h u

def coreDen (n h l : ℕ) : ℚ[X] := ∏ u ∈ Finset.range l, blockDen n h u

lemma poch_blocks (a d n l : ℕ) :
    poch a d (l*n) = ∏ u ∈ Finset.range l, poch (a+d*(u*n)) d n := by
  induction l with
  | zero => simp [poch]
  | succ l ih =>
    rw [Nat.succ_mul, poch_add, ih, Finset.prod_range_succ]

/-- This equality connects the cancelled representative to the literal
Pochhammer ratio; it is not a model assigned only at roots. -/
theorem core_fraction_identity (n h l : ℕ) (hn : 0<n) (hh : n=2*h+1) :
    poch 2 4 (l*n) / poch 4 4 (l*n) = embed (coreNum n h l) / embed (coreDen n h l) := by
  rw [poch_blocks, poch_blocks, coreNum, coreDen, map_prod, map_prod,
    ← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro u _
  simpa only [Nat.add_comm 2, Nat.add_comm 4] using block_fraction_identity n h u hn hh

lemma half_ratio_product (l : ℕ) :
    (∏ u ∈ Finset.range l, ((2*(u:ℚ)+1)/(2*(u:ℚ)+2))) =
      halfPoch l / (Nat.factorial l : ℚ) := by
  induction l with
  | zero => simp [halfPoch]
  | succ l ih => rw [Finset.prod_range_succ, ih, half_ratio_step]

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma coreNum_aeval_ne_zero (n h l : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) : aeval z (coreNum n h l) ≠ 0 := by
  simp only [coreNum, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun u _ => blockNum_aeval_ne_zero n h u hh hz)

lemma coreDen_aeval_ne_zero (n h l : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) : aeval z (coreDen n h l) ≠ 0 := by
  simp only [coreDen, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun u _ => blockDen_aeval_ne_zero n h u hh hz)

theorem core_regular (n h l : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    Regular (cyclotomic n ℚ) (poch 2 4 (l*n) / poch 4 4 (l*n)) := by
  rw [core_fraction_identity n h l hn hh]
  have hb := coreDen_aeval_ne_zero n h l hh hz
  apply regular_of_fraction
  · intro he; exact hb (by rw [he, map_zero])
  · exact coprime_cyclotomic_of_aeval_ne_zero hn hz _ hb

/-- The whole-block value in the source's literal half-factorial normalization. -/
theorem core_value (n h l : ℕ) (hh : n=2*h+1) (hz : IsPrimitiveRoot z n) :
    aeval z (coreNum n h l) / aeval z (coreDen n h l) =
      algebraMap ℚ K (halfPoch l / (Nat.factorial l : ℚ)) := by
  rw [coreNum, coreDen, map_prod, map_prod, ← Finset.prod_div_distrib]
  calc
    _ = ∏ u ∈ Finset.range l, algebraMap ℚ K ((2*(u:ℚ)+1)/(2*(u:ℚ)+2)) := by
      apply Finset.prod_congr rfl
      intro u _
      simpa using block_value n h u hh hz
    _ = algebraMap ℚ K (∏ u ∈ Finset.range l, ((2*(u:ℚ)+1)/(2*(u:ℚ)+2))) := by
      rw [map_prod]
    _ = _ := by rw [half_ratio_product]

/-- Uniform logarithmic Euler derivative of the cancelled long products. -/
theorem core_log_derivative (n h l : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    eulerLog z (coreNum n h l)-eulerLog z (coreDen n h l) =
      (l:K)*(-(n:K)^2-4*(n:K)*halfHarmonic z h) := by
  rw [coreNum, coreDen,
    eulerLog_prod _ _ _ (fun u _ => blockNum_aeval_ne_zero n h u hh hz),
    eulerLog_prod _ _ _ (fun u _ => blockDen_aeval_ne_zero n h u hh hz),
    ← Finset.sum_sub_distrib]
  simp only [block_log_derivative n h _ hh hz, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-- The actual first Euler derivative as a polynomial-fraction witness:
D R_(ln)(z) = l*c_l*C. The denominator has already been proved a unit. -/
theorem core_euler_derivative (n h l : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    z * (aeval z (coreNum n h l).derivative * aeval z (coreDen n h l) -
      aeval z (coreNum n h l) * aeval z (coreDen n h l).derivative) /
      (aeval z (coreDen n h l))^2 =
      (l:K) * algebraMap ℚ K (halfPoch l / (Nat.factorial l : ℚ)) *
        (-(n:K)^2-4*(n:K)*halfHarmonic z h) := by
  rw [quotient_euler_cross _ _ _ (coreNum_aeval_ne_zero n h l hh hz)
    (coreDen_aeval_ne_zero n h l hh hz), core_value n h l hh hz,
    core_log_derivative n h l hh hz]
  ring

/-- The real numerator cross polynomial for two representatives has a
vanishing first derivative when their quotient values and Euler derivatives
agree. This is the direct interface to the stage-1 square-divisibility bridge. -/
lemma fraction_cross_derivative_zero (A B C D : ℚ[X]) (hz0 : z≠0)
    (hB : aeval z B ≠ 0) (hD : aeval z D ≠ 0)
    (hv : aeval z A / aeval z B = aeval z C / aeval z D)
    (hd : z * (aeval z A.derivative * aeval z B - aeval z A * aeval z B.derivative) /
        (aeval z B)^2 =
      z * (aeval z C.derivative * aeval z D - aeval z C * aeval z D.derivative) /
        (aeval z D)^2) :
    aeval z (A*D-C*B) = 0 ∧ aeval z (A*D-C*B).derivative = 0 := by
  have hval := (div_eq_div_iff hB hD).mp hv
  have hd' := (div_eq_div_iff (pow_ne_zero 2 hB) (pow_ne_zero 2 hD)).mp hd
  constructor
  · simp only [map_sub, map_mul]
    exact sub_eq_zero.mpr hval
  · simp only [derivative_mul, map_sub, map_add, map_mul]
    apply (mul_left_cancel₀ (mul_ne_zero hz0 (mul_ne_zero hB hD)))
    linear_combination hd' + z * (aeval z B.derivative * aeval z D +
      aeval z B * aeval z D.derivative) * hval

end Roots
end
end Guo62
```

### `GuoJet.lean`

```lean
import GuoCore

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

/-- A first Euler jet of an actual rational function, with a unit denominator. -/
def HasJet (z : K) (f : RatFunc ℚ) (v d : K) : Prop :=
  ∃ A B : ℚ[X], aeval z B ≠ 0 ∧ f = embed A / embed B ∧
    aeval z A = v * aeval z B ∧
    z * aeval z A.derivative = d * aeval z B + v * z * aeval z B.derivative

lemma HasJet.fraction (A B : ℚ[X]) (hB : aeval z B ≠ 0) :
    HasJet z (embed A / embed B) (aeval z A / aeval z B)
      (z * (aeval z A.derivative * aeval z B -
        aeval z A * aeval z B.derivative) / (aeval z B)^2) := by
  refine ⟨A, B, hB, rfl, ?_, ?_⟩
  · field_simp
  · field_simp
    ring

lemma HasJet.const (c : ℚ) :
    HasJet z (algebraMap ℚ (RatFunc ℚ) c) (algebraMap ℚ K c) 0 := by
  refine ⟨C c, 1, by simp, ?_, by simp, by simp⟩
  simp [embed]

lemma HasJet.add {f g : RatFunc ℚ} {v d w e : K}
    (hf : HasJet z f v d) (hg : HasJet z g w e) : HasJet z (f+g) (v+w) (d+e) := by
  obtain ⟨A,B,hB,rfl,hv,hd⟩ := hf
  obtain ⟨C,D,hD,rfl,hw,he⟩ := hg
  have hBn : B ≠ 0 := by intro h; exact hB (by simp [h])
  have hDn : D ≠ 0 := by intro h; exact hD (by simp [h])
  refine ⟨A*D+C*B, B*D, by simpa using mul_ne_zero hB hD, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul]
    field_simp [RatFunc.algebraMap_ne_zero hBn, RatFunc.algebraMap_ne_zero hDn]
  · simp only [map_add, map_mul]
    rw [hv, hw]
    ring
  · simp only [derivative_mul, map_add, map_mul]
    linear_combination (aeval z D)*hd + (aeval z B)*he +
      z*(aeval z D.derivative)*hv + z*(aeval z B.derivative)*hw

lemma HasJet.mul {f g : RatFunc ℚ} {v d w e : K}
    (hf : HasJet z f v d) (hg : HasJet z g w e) :
    HasJet z (f*g) (v*w) (d*w+v*e) := by
  obtain ⟨A,B,hB,rfl,hv,hd⟩ := hf
  obtain ⟨C,D,hD,rfl,hw,he⟩ := hg
  refine ⟨A*C, B*D, by simpa using mul_ne_zero hB hD, ?_, ?_, ?_⟩
  · simp only [map_mul, div_mul_div_comm]
  · simp only [map_mul]
    rw [hv, hw]
    ring
  · simp only [derivative_mul, map_add, map_mul]
    rw [hv, hw]
    linear_combination w*(aeval z D)*hd + v*(aeval z B)*he

lemma HasJet.sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) (v d : ι → K)
    (h : ∀ i ∈ s, HasJet z (f i) (v i) (d i)) :
    HasJet z (∑ i ∈ s, f i) (∑ i ∈ s, v i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HasJet.const (z := z) 0)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma HasJet.congSq {n : ℕ} (hn : 0<n) (hz : IsPrimitiveRoot z n)
    {f g : RatFunc ℚ} {v d : K} (hf : HasJet z f v d) (hg : HasJet z g v d) :
    CongSq n f g := by
  obtain ⟨A,B,hB,rfl,hv,hd⟩ := hf
  obtain ⟨C,D,hD,rfl,hw,he⟩ := hg
  apply (congSq_fractions_iff n A B C D
    (by intro h; exact hB (by simp [h])) (by intro h; exact hD (by simp [h]))
    (coprime_cyclotomic_of_aeval_ne_zero hn hz _ hB)
    (coprime_cyclotomic_of_aeval_ne_zero hn hz _ hD)).mpr
  apply cyclotomic_square_dvd_of_aeval_zero hn hz
  · simp only [map_sub, map_mul]
    rw [hv, hw]
    ring
  · have hz0 := hz.ne_zero hn.ne'
    apply (mul_left_cancel₀ hz0)
    simp only [derivative_mul, map_sub, map_add, map_mul, mul_zero]
    linear_combination (aeval z D)*hd - (aeval z B)*he +
      z*(aeval z D.derivative)*hv - z*(aeval z B.derivative)*hw

end
end Guo62
```

### `GuoShift.lean`

```lean
import GuoCore

namespace Guo62
open Polynomial
noncomputable section

def term (k : ℕ) : RatFunc ℚ :=
  (1+q^(4*k+1)) * (poch 2 4 k)^3 * q^k / ((1+q)*(poch 4 4 k)^3)

def shiftedNum (n l s : ℕ) : ℚ[X] := pochPoly (4*(l*n)+2) 4 s

def shiftedDen (n l s : ℕ) : ℚ[X] := pochPoly (4*(l*n)+4) 4 s

/-- Logarithmic derivative error of the shifted Pochhammer prefix. -/
def shiftH {K : Type*} [Field K] (z : K) (s : ℕ) : K :=
  ∑ j ∈ Finset.range s, (rootFrac (z^(4*(j+1))) - rootFrac (z^(4*j+2)))

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma shiftedDen_aeval_ne_zero (n l s : ℕ) (ho : Odd n) (hs : s<n)
    (hz : IsPrimitiveRoot z n) : aeval z (shiftedDen n l s) ≠ 0 := by
  rw [shiftedDen, pochPoly_aeval]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [denominator_residue_low n l j hz.pow_eq_one]
  have hQ := fourth_power_primitive ho hz
  simpa only [pow_mul] using one_sub_root_pow_ne_zero hQ
    (Nat.not_dvd_of_pos_of_lt (by omega) (by have := Finset.mem_range.mp hj; omega : j+1<n))

lemma shiftedNum_aeval_ne_zero (n h l s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) : aeval z (shiftedNum n l s) ≠ 0 := by
  rw [shiftedNum, pochPoly_aeval]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [low_residue n h l j hh hz.pow_eq_one]
  exact (block_residue_units n h hh hz).2 j (by have := Finset.mem_range.mp hj; omega)

lemma shifted_values (n l s : ℕ) (hz : z^n=1) :
    aeval z (shiftedNum n l s) = aeval z (pochPoly 2 4 s) ∧
    aeval z (shiftedDen n l s) = aeval z (pochPoly 4 4 s) := by
  simp only [shiftedNum, shiftedDen, pochPoly_aeval]
  constructor <;> apply Finset.prod_congr rfl <;> intro j _
  · rw [show 4*(l*n)+2+4*j=4*(l*n)+(2+4*j) by omega, block_pow n l _ hz]
  · rw [show 4*(l*n)+4+4*j=4*(l*n)+(4+4*j) by omega, block_pow n l _ hz]

/-- Source-specific shift error, derived from the actual polynomial prefixes.
It is uniform in n,l,s under the admissible half-block bound. -/
theorem shifted_log_derivative (n h l s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    (eulerLog z (shiftedNum n l s)-eulerLog z (shiftedDen n l s)) -
      (eulerLog z (pochPoly 2 4 s)-eulerLog z (pochPoly 4 4 s)) =
        4*(l:K)*(n:K)*shiftH z s := by
  have ho : Odd n := ⟨h, by omega⟩
  have hA := shiftedNum_aeval_ne_zero n h l s hh hs hz
  have hB := shiftedDen_aeval_ne_zero n l s ho (by omega) hz
  obtain ⟨hvA, hvB⟩ := shifted_values n l s hz.pow_eq_one
  have hA0 : aeval z (pochPoly 2 4 s) ≠ 0 := hvA ▸ hA
  have hB0 : aeval z (pochPoly 4 4 s) ≠ 0 := hvB ▸ hB
  rw [shiftedNum, shiftedDen, eulerLog_pochPoly _ _ _ hA,
    eulerLog_pochPoly _ _ _ hB, eulerLog_pochPoly _ _ _ hA0,
    eulerLog_pochPoly _ _ _ hB0, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    shiftH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show 4*(l*n)+2+4*j=4*(l*n)+(2+4*j) by omega, block_pow n l _ hz.pow_eq_one,
    denominator_residue_low n l j hz.pow_eq_one]
  push_cast
  rw [show 2+4*j=4*j+2 by omega, show 4+4*j=4*(j+1) by omega]
  ring

end Roots
end
end Guo62
```

### `GuoJetOperations.lean`

```lean
import GuoJet

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma HasJet.neg {f : RatFunc ℚ} {v d : K} (hf : HasJet z f v d) :
    HasJet z (-f) (-v) (-d) := by
  have h := (HasJet.const (z := z) (-1)).mul hf
  simpa using h

lemma HasJet.sub {f g : RatFunc ℚ} {v d w e : K}
    (hf : HasJet z f v d) (hg : HasJet z g w e) : HasJet z (f-g) (v-w) (d-e) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma HasJet.inv {f : RatFunc ℚ} {v d : K} (hf : HasJet z f v d) (hv0 : v≠0) :
    HasJet z f⁻¹ v⁻¹ (-d/v^2) := by
  obtain ⟨A,B,hB,rfl,hv,hd⟩ := hf
  have hA : aeval z A≠0 := by rw [hv]; exact mul_ne_zero hv0 hB
  refine ⟨B,A,hA,by simp,?_,?_⟩
  · rw [hv]
    field_simp
  · rw [hv]
    apply (mul_left_cancel₀ hv0)
    field_simp
    linear_combination -hd

lemma HasJet.div {f g : RatFunc ℚ} {v d w e : K}
    (hf : HasJet z f v d) (hg : HasJet z g w e) (hw : w≠0) :
    HasJet z (f/g) (v/w) ((d*w-v*e)/w^2) := by
  have h := hf.mul (hg.inv hw)
  convert h using 1
  · exact div_eq_mul_inv _ _
  · exact div_eq_mul_inv _ _
  · field_simp
    ring

lemma HasJet.poly (P : ℚ[X]) : HasJet z (embed P) (aeval z P) (z*aeval z P.derivative) := by
  refine ⟨P,1,by simp,by simp,by simp,by simp⟩

lemma HasJet.qpow (a : ℕ) : HasJet z (q^a) (z^a) ((a:K)*z^a) := by
  have h := HasJet.poly (z := z) (X^a)
  convert h using 1
  · simp [embed]
  · simp
  · cases a with
    | zero => simp
    | succ a =>
      rw [derivative_X_pow_succ]
      simp only [map_mul, map_pow, aeval_X, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

lemma HasJet.prod {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) (v d : ι → K)
    (h : ∀ i ∈ s, HasJet z (f i) (v i) (d i)) :
    ∃ e, HasJet z (∏ i ∈ s, f i) (∏ i ∈ s, v i) e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simpa using HasJet.const (z := z) 1⟩
  | @insert i s hi ih =>
    obtain ⟨e,he⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨d i*(∏ j ∈ s, v j)+v i*e,?_⟩
    simpa only [Finset.prod_insert hi] using (h i (Finset.mem_insert_self _ _)).mul he

end
end Guo62
```

### `GuoRegularity.lean`

```lean
import GuoShift
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace Guo62
open Polynomial
noncomputable section

lemma Regular.pow {p : ℚ[X]} {f : RatFunc ℚ} (hf : Regular p f) (k : ℕ) :
    Regular p (f^k) := by
  induction k with
  | zero => simpa using Regular.one p
  | succ k ih => simpa only [pow_succ] using ih.mul hf

lemma ratio_split (n l s : ℕ) :
    poch 2 4 (l*n+s) / poch 4 4 (l*n+s) =
      (poch 2 4 (l*n) / poch 4 4 (l*n)) *
        (embed (shiftedNum n l s) / embed (shiftedDen n l s)) := by
  simp only [shiftedNum, shiftedDen, show embed=algebraMap ℚ[X] (RatFunc ℚ) from rfl,
    pochPoly_map, poch_add]
  rw [show 2+4*(l*n)=4*(l*n)+2 by omega, show 4+4*(l*n)=4*(l*n)+4 by omega]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma term_factorization (k : ℕ) :
    term k = (embed (1+X^(4*k+1)) / embed (1+X)) * embed (X^k) *
      (poch 2 4 k / poch 4 4 k)^3 := by
  simp only [term, map_add, map_pow, map_one, embed, RatFunc.algebraMap_X,
    div_eq_mul_inv, mul_inv_rev, mul_pow]
  ring

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma source_ratio_regular_root (n h l s : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (hs : s<n) (hz : IsPrimitiveRoot z n) :
    Regular (cyclotomic n ℚ) (poch 2 4 (l*n+s) / poch 4 4 (l*n+s)) := by
  rw [ratio_split]
  apply (core_regular n h l hn hh hz).mul
  have ho : Odd n := ⟨h, by omega⟩
  have hb := shiftedDen_aeval_ne_zero n l s ho hs hz
  apply regular_of_fraction
  · intro he; exact hb (by rw [he, map_zero])
  · exact coprime_cyclotomic_of_aeval_ne_zero hn hz _ hb

lemma source_term_regular_root (n h k : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) : Regular (cyclotomic n ℚ) (term k) := by
  have ho : Odd n := ⟨h, by omega⟩
  have hr := source_ratio_regular_root n h (k/n) (k%n) hn hh (Nat.mod_lt k hn) hz
  rw [Nat.mul_comm (k/n) n, Nat.div_add_mod k n] at hr
  rw [term_factorization]
  apply Regular.mul _ (hr.pow 3)
  apply Regular.mul _ (Regular.poly _ _)
  exact regular_of_fraction (by simpa using one_add_X_pow_ne_zero 1)
    (by simpa using plus_binomial_coprime_cyclotomic hn ho hz 1)

end Roots

/-- One of the exact stage-1 remaining obligations, now without any extra
primitive-root or cancellation hypotheses. All k, including k>=n, are covered. -/
theorem source_term_regular (n k : ℕ) (hn : 1<n) (h4 : n%4=1) :
    Regular (cyclotomic n ℚ) (term k) := by
  have hh := (admissible_half n hn h4).1
  exact source_term_regular_root n ((n-1)/2) k (by omega) (by omega)
    (Complex.isPrimitiveRoot_exp n (by omega))

/-- Regularity of the literal full LHS, for arbitrary m. -/
theorem source_lhs_regular (m n : ℕ) (hn : 1<n) (h4 : n%4=1) :
    Regular (cyclotomic n ℚ) (lhs m n) := by
  exact Regular.sum _ _ (fun k _ => source_term_regular n k hn h4)

end
end Guo62
```

### `GuoShiftReflection.lean`

```lean
import GuoShift

namespace Guo62
noncomputable section

lemma sum_reverse_tail {K : Type*} [AddCommGroup K] (f : ℕ → K) (h s : ℕ) (hs : s≤h) :
    (∑ j ∈ Finset.range s, f (h-j)) =
      (∑ j ∈ Finset.range h, f (j+1)) - ∑ j ∈ Finset.range (h-s), f (j+1) := by
  have he := Finset.sum_range_add (fun j => f (j+1)) (h-s) s
  rw [Nat.sub_add_cancel hs] at he
  have ht : (∑ j ∈ Finset.range s, f (h-j)) =
      ∑ j ∈ Finset.range s, f (h-s+j+1) := by
    rw [← Finset.sum_range_reflect (fun j => f (h-s+j+1)) s]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have := Finset.mem_range.mp hj
    omega
  rw [ht]
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he.symm)

section Roots
variable {K : Type*} [Field K] {z : K}

/-- Explicit source shift-error expression as two complementary harmonic sums. -/
theorem shiftH_formula (n h s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    shiftH z s = (s:K)+halfHarmonic z s+halfHarmonic z h-halfHarmonic z (h-s) := by
  have ht : ∀ j<s, rootFrac (z^(4*j+2)) = -1-rootFrac (z^(4*(h-j))) := by
    intro j hj
    have hjh : j<h := by omega
    rw [show 4*j+2=4*(0*n)+2+4*j by omega,
      low_residue n h 0 j hh hz.pow_eq_one, upper_residue_inverse n h j hh hz hjh]
    apply rootFrac_inv
    · exact pow_ne_zero _ (hz.ne_zero (by omega))
    · have ho : Odd n := ⟨h, by omega⟩
      simpa only [pow_mul] using one_sub_root_pow_ne_zero (fourth_power_primitive ho hz)
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : h-j<n))
  have he : shiftH z s = (s:K)+halfHarmonic z s+
      ∑ j ∈ Finset.range s, rootFrac (z^(4*(h-j))) := by
    unfold shiftH halfHarmonic
    calc
      _ = ∑ j ∈ Finset.range s, (1+rootFrac (z^(4*(j+1)))+rootFrac (z^(4*(h-j)))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ht j (Finset.mem_range.mp hj)]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
  rw [he, sum_reverse_tail (fun r => rootFrac (z^(4*r))) h s hs]
  change (s:K)+halfHarmonic z s+(halfHarmonic z h-halfHarmonic z (h-s)) = _
  ring

/-- The actual H_s appearing in the uniform prefix derivative pairs to a
constant; this is no longer an assumed error-family condition. -/
theorem shiftH_reflection (n h s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    shiftH z s+shiftH z (h-s) = (h:K)+2*halfHarmonic z h := by
  rw [shiftH_formula n h s hh hs hz,
    shiftH_formula n h (h-s) hh (Nat.sub_le _ _) hz,
    Nat.sub_sub_self hs, Nat.cast_sub hs]
  ring

variable [CharZero K]

/-- Plus-weight reflection. Oddness ensures the real denominator is nonzero. -/
lemma plus_weight_reflection (n h s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    z^(4*s+1)/(1+z^(4*s+1)) + z^(4*(h-s)+1)/(1+z^(4*(h-s)+1)) = 1 := by
  have hn : n≠0 := by omega
  have ho : Odd n := ⟨h, by omega⟩
  have ha := one_add_root_pow_ne_zero ho hz (4*s+1)
  have hb := one_add_root_pow_ne_zero ho hz (4*(h-s)+1)
  have he : z^(4*s+1)*z^(4*(h-s)+1)=1 := by
    rw [← pow_add, show 4*s+1+(4*(h-s)+1)=n*2 by omega,
      pow_mul, hz.pow_eq_one, one_pow]
  field_simp
  linear_combination he

/-- The concrete L_s from the written proof. -/
def shiftL (z : K) (s : ℕ) : K := z^(4*s+1)/(1+z^(4*s+1))+3*shiftH z s

theorem shiftL_reflection (n h s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    shiftL z s+shiftL z (h-s)=1+3*(h:K)+6*halfHarmonic z h := by
  unfold shiftL
  linear_combination plus_weight_reflection n h s hh hs hz + 3*shiftH_reflection n h s hh hs hz

end Roots
end
end Guo62
```

### `GuoReciprocityAtOne.lean`

```lean
import GuoShiftReflection
import GuoReciprocity
import GuoFirstOrder

namespace Guo62
noncomputable section
variable {K : Type*} [Field K] {z : K}

lemma one_sub_inv_ne_zero (x : K) (hx : 1-x≠0) : 1-x⁻¹≠0 := by
  intro he
  have hi : x⁻¹=1 := (sub_eq_zero.mp he).symm
  have := congrArg (Inv.inv : K → K) hi
  simp only [inv_inv, inv_one] at this
  exact hx (by rw [this, sub_self])

lemma shiftRatio_one_ne_zero (Q : K) (n h s : ℕ) (hh : h<n) (hs : s≤h)
    (hQ : IsPrimitiveRoot Q n) : shiftRatio Q 1 h s ≠ 0 := by
  unfold shiftRatio prefixProd
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjh : j<h := by have := Finset.mem_range.mp hj; omega
  simp only [one_mul]
  apply div_ne_zero
  · rw [show (j:ℤ)-(h:ℤ)=-((h-j:ℕ):ℤ) by omega, zpow_neg, zpow_natCast]
    exact one_sub_inv_ne_zero _ (one_sub_root_pow_ne_zero hQ
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : h-j<n)))
  · rw [show (j:ℤ)+1=((j+1:ℕ):ℤ) by omega, zpow_natCast]
    exact one_sub_root_pow_ne_zero hQ (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : j+1<n))

variable [CharZero K]

lemma shiftTerm_one_ne_zero (n h s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) : shiftTerm z (z^4) 1 h s ≠ 0 := by
  have ho : Odd n := ⟨h, by omega⟩
  have hz0 := hz.ne_zero (by omega : n≠0)
  unfold shiftTerm
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply div_ne_zero
      · simpa only [one_mul, ← pow_mul, ← pow_succ'] using
          one_add_root_pow_ne_zero ho hz (4*s+1)
      · simpa only [pow_one] using one_add_root_pow_ne_zero ho hz 1
    · exact pow_ne_zero _ hz0
  · exact pow_ne_zero _ (shiftRatio_one_ne_zero (z^4) n h s (by omega) hs
      (fourth_power_primitive ho hz))

/-- P(1)=1 from the nonzero central summand (h even), avoiding a second
long-product exponent sum. This cancels one summand, never the total sum. -/
theorem reciprocity_prefactor_one (n h : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (he : Even h) (hz : IsPrimitiveRoot z n) :
    (z^h/z)*(shiftRatio (z^4) 1 h h)^3=1 := by
  obtain ⟨a, ha⟩ := he
  have ho : Odd n := ⟨h, by omega⟩
  have hz0 := hz.ne_zero hn.ne'
  have hQ := fourth_power_primitive ho hz
  obtain ⟨hA, hB⟩ := shift_factors_at_one hn hQ h (by omega)
  obtain ⟨hQh, hQh1⟩ := root_half_relations hn hz h hh
  have ht := shiftTerm_reflection z (z^4) 1 h a hz0 (pow_ne_zero 4 hz0)
    one_ne_zero (by omega) rfl hQh hQh1
    (fun j hj => by simpa only [one_mul] using hA j (by omega))
    (fun j hj => by simpa only [one_mul] using hB j (by omega))
  rw [show h-a=a by omega] at ht
  simp only [one_mul, inv_one] at ht
  apply (mul_right_cancel₀ (shiftTerm_one_ne_zero n h a hh (by omega) hz))
  simpa only [one_mul] using ht.symm

/-- Fully specialized summand reflection, with P(1)=1 proved internally. -/
theorem shiftTerm_one_reflection (n h s : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (he : Even h) (hs : s≤h) (hz : IsPrimitiveRoot z n) :
    shiftTerm z (z^4) 1 h (h-s)=shiftTerm z (z^4) 1 h s := by
  have ho : Odd n := ⟨h, by omega⟩
  have hz0 := hz.ne_zero hn.ne'
  have hQ := fourth_power_primitive ho hz
  obtain ⟨hA, hB⟩ := shift_factors_at_one hn hQ h (by omega)
  obtain ⟨hQh, hQh1⟩ := root_half_relations hn hz h hh
  have ht := shiftTerm_reflection z (z^4) 1 h s hz0 (pow_ne_zero 4 hz0)
    one_ne_zero hs rfl hQh hQh1
    (fun j hj => by simpa only [one_mul] using hA j (by omega))
    (fun j hj => by simpa only [one_mul] using hB j (by omega))
  simpa only [one_mul, inv_one, reciprocity_prefactor_one n h hn hh he hz] using ht

/-- Concrete reflected error cancellation. Neither t-reflection nor L-reflection
is left as a hypothesis; no division by the finite sum occurs. -/
theorem source_shift_error_zero (n h : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (he : Even h) (hz : IsPrimitiveRoot z n) :
    ∑ s ∈ Finset.range (h+1), shiftTerm z (z^4) 1 h s *
      (3*(-(n:K)^2-4*(n:K)*halfHarmonic z h)+(n:K)+4*(n:K)*shiftL z s)=0 := by
  apply half_block_error_zero h (n:K) (halfHarmonic z h)
    (fun s => shiftTerm z (z^4) 1 h s) (shiftL z)
  · have hc : (n:K)=2*(h:K)+1 := by exact_mod_cast hh
    linear_combination -hc
  · intro s hs
    exact shiftTerm_one_reflection n h s hn hh he hs hz
  · intro s hs
    exact shiftL_reflection n h s hh hs hz

end
end Guo62
```

### `GuoRhsRegularity.lean`

```lean
import GuoRegularity
import GuoCongSqAlgebra

namespace Guo62
open Polynomial
noncomputable section

def rhsRest (n : ℕ) : ℚ[X] :=
  ∏ j ∈ (Finset.range ((n-1)/2)).erase (n/4-1), (1-X^(5+4*j))

lemma rhs_poch_split (n : ℕ) (hn : 1<n) (h4 : n%4=1) :
    poch 5 4 ((n-1)/2) = (1-q^n) * embed (rhsRest n) := by
  have hj : n/4-1 ∈ Finset.range ((n-1)/2) := Finset.mem_range.mpr (by omega)
  have hexp : 5+4*(n/4-1)=n := by omega
  have hp := Finset.mul_prod_erase (Finset.range ((n-1)/2))
    (fun j => (1-q^(5+4*j))) hj
  simpa only [poch, rhsRest, map_prod, map_sub, map_one, map_pow,
    embed, RatFunc.algebraMap_X, hexp] using hp.symm

lemma rhs_fraction (n : ℕ) (hn : 1<n) (h4 : n%4=1) :
    qInt2 n * poch 3 4 ((n-1)/2) / poch 5 4 ((n-1)/2) * (q^((n-1)/2))⁻¹ =
    embed ((1+X^n)*pochPoly 3 4 ((n-1)/2)) /
      embed ((1-X^2)*rhsRest n*X^((n-1)/2)) := by
  rw [qInt2_eq_fraction, rhs_poch_split n hn h4]
  have hfac : 1-q^(2*n)=(1-q^n)*(1+q^n) := by
    rw [show 2*n=n*2 by omega, pow_mul]
    ring
  rw [hfac]
  simp only [map_mul, map_add, map_one, map_pow, map_sub, embed,
    RatFunc.algebraMap_X, pochPoly_map]
  field_simp [one_sub_q_pow_ne_zero (by omega : 0<n)]

lemma rhsRest_aeval_ne_zero {K : Type*} [Field K] [CharZero K] {z : K}
    (n : ℕ) (hn : 1<n) (h4 : n%4=1) (hz : IsPrimitiveRoot z n) :
    aeval z (rhsRest n)≠0 := by
  simp only [rhsRest, map_prod, map_sub, map_one, map_pow, aeval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  obtain ⟨hne,hj⟩ := Finset.mem_erase.mp hj
  have hj' := Finset.mem_range.mp hj
  apply one_sub_root_pow_ne_zero hz
  rintro ⟨a,ha⟩
  have hapos : 0<a := by nlinarith
  have hbound : 5+4*j<2*n := by omega
  have halt : a<2 := by nlinarith
  have ha1 : a=1 := by omega
  rw [ha1,mul_one] at ha
  apply hne
  omega

/-- The RHS denominator has its unique cyclotomic zero explicitly cancelled. -/
theorem source_rhs_regular (m n : ℕ) (_hm : 0<m) (hn : 1<n) (h4 : n%4=1) :
    Regular (cyclotomic n ℚ) (rhs m n) := by
  unfold rhs
  apply Regular.mul _ (Regular.const _ _)
  rw [rhs_fraction n hn h4]
  let z := Complex.exp (2*Real.pi*Complex.I/n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n (by omega)
  have hz0 := hz.ne_zero (by omega : n≠0)
  have hb : aeval z ((1-X^2)*rhsRest n*X^((n-1)/2))≠0 := by
    simp only [map_mul, map_sub, map_one, map_pow, aeval_X]
    exact mul_ne_zero (mul_ne_zero
      (one_sub_root_pow_ne_zero hz (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)))
      (rhsRest_aeval_ne_zero n hn h4 hz)) (pow_ne_zero _ hz0)
  exact regular_of_fraction (by intro h; exact hb (by simp [h]))
    (coprime_cyclotomic_of_aeval_ne_zero (by omega) hz _ hb)

end
end Guo62
```

### `GuoSameJet.lean`

```lean
import GuoJetOperations

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

/-- Two faithful fractions have the same first jet and the specified value. -/
def SameJet (z : K) (f g : RatFunc ℚ) (v : K) : Prop :=
  ∃ d, HasJet z f v d ∧ HasJet z g v d

lemma SameJet.refl {f : RatFunc ℚ} {v d : K} (h : HasJet z f v d) : SameJet z f f v :=
  ⟨d,h,h⟩

lemma SameJet.mul {f g a b : RatFunc ℚ} {v w : K}
    (h : SameJet z f g v) (h' : SameJet z a b w) : SameJet z (f*a) (g*b) (v*w) := by
  obtain ⟨d,hf,hg⟩ := h
  obtain ⟨e,ha,hb⟩ := h'
  exact ⟨d*w+v*e,hf.mul ha,hg.mul hb⟩

lemma SameJet.div {f g a b : RatFunc ℚ} {v w : K}
    (h : SameJet z f g v) (h' : SameJet z a b w) (hw : w≠0) :
    SameJet z (f/a) (g/b) (v/w) := by
  obtain ⟨d,hf,hg⟩ := h
  obtain ⟨e,ha,hb⟩ := h'
  exact ⟨(d*w-v*e)/w^2,hf.div ha hw,hg.div hb hw⟩

lemma SameJet.prod {ι : Type*} (s : Finset ι) (f g : ι → RatFunc ℚ) (v : ι → K)
    (h : ∀ i∈s, SameJet z (f i) (g i) (v i)) :
    SameJet z (∏ i ∈ s, f i) (∏ i ∈ s, g i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SameJet.refl (HasJet.const (z := z) 1)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma SameJet.congSq {n : ℕ} (hn : 0<n) (hz : IsPrimitiveRoot z n)
    {f g : RatFunc ℚ} {v : K} (h : SameJet z f g v) : CongSq n f g := by
  obtain ⟨d,hf,hg⟩ := h
  exact hf.congSq hn hz hg

lemma HasJet.qzpow (hz : z≠0) (a : ℤ) : HasJet z (q^a) (z^a) ((a:K)*z^a) := by
  cases a with
  | ofNat a => simpa only [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_natCast] using HasJet.qpow (z := z) a
  | negSucc a =>
    have h := (HasJet.qpow (z := z) (a+1)).inv (pow_ne_zero _ hz)
    simp only [zpow_negSucc]
    convert h using 1
    push_cast
    field_simp


end
end Guo62
```

### `GuoTermWitness.lean`

```lean
import GuoRegularity
import GuoShiftReflection

namespace Guo62
open Polynomial
noncomputable section

def termNum (n h l s : ℕ) : ℚ[X] :=
  ((1+X^(4*(l*n+s)+1))*X^(l*n+s)) * (coreNum n h l * shiftedNum n l s)^3

def termDen (n h l s : ℕ) : ℚ[X] :=
  (1+X) * (coreDen n h l * shiftedDen n l s)^3

theorem term_fraction_identity (n h l s : ℕ) (hn : 0<n) (hh : n=2*h+1) :
    term (l*n+s) = embed (termNum n h l s) / embed (termDen n h l s) := by
  rw [term_factorization, ratio_split, core_fraction_identity n h l hn hh]
  simp only [termNum, termDen, map_mul, map_pow, div_eq_mul_inv, mul_inv_rev, mul_pow]
  ring

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma eulerLog_pow (P : ℚ[X]) (hp : aeval z P≠0) (k : ℕ) :
    eulerLog z (P^k) = (k:K)*eulerLog z P := by
  induction k with
  | zero => simp [eulerLog_one]
  | succ k ih =>
    rw [pow_succ, eulerLog_mul _ _ _ (by simpa only [map_pow] using pow_ne_zero k hp) hp, ih]
    push_cast
    ring

lemma eulerLog_monomial (k : ℕ) (hz : z≠0) : eulerLog z (X^k) = (k:K) := by
  have he := congrArg (aeval z) (euler_X_pow k)
  simp only [map_mul, aeval_X, map_pow, aeval_C, eq_ratCast, Rat.cast_natCast] at he
  simp only [eulerLog, map_pow, aeval_X]
  rw [he, mul_div_cancel_right₀ _ (pow_ne_zero k hz)]

lemma eulerLog_plus (k : ℕ) : eulerLog z (1+X^k) = (k:K)*z^k/(1+z^k) := by
  have he := congrArg (aeval z) (euler_X_pow k)
  simp only [map_mul, aeval_X, map_pow, aeval_C, eq_ratCast, Rat.cast_natCast] at he
  simp only [eulerLog, derivative_one, zero_add, map_add,
    map_one, map_pow, aeval_X]
  rw [he]

lemma termDen_aeval_ne_zero (n h l s : ℕ) (hh : n=2*h+1) (hs : s<n)
    (hz : IsPrimitiveRoot z n) : aeval z (termDen n h l s)≠0 := by
  have ho : Odd n := ⟨h, by omega⟩
  simp only [termDen, map_mul, map_pow, map_add, map_one, aeval_X]
  exact mul_ne_zero (by simpa only [pow_one] using one_add_root_pow_ne_zero ho hz 1)
    (pow_ne_zero 3 (mul_ne_zero (coreDen_aeval_ne_zero n h l hh hz)
      (shiftedDen_aeval_ne_zero n l s ho hs hz)))

lemma termNum_aeval_ne_zero (n h l s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) : aeval z (termNum n h l s)≠0 := by
  have ho : Odd n := ⟨h, by omega⟩
  simp only [termNum, map_mul, map_pow, map_add, map_one, aeval_X]
  exact mul_ne_zero (mul_ne_zero (one_add_root_pow_ne_zero ho hz _) (pow_ne_zero _ (hz.ne_zero (by omega))))
    (pow_ne_zero 3 (mul_ne_zero (coreNum_aeval_ne_zero n h l hh hz)
      (shiftedNum_aeval_ne_zero n h l s hh hs hz)))

/-- Complete logarithmic derivative formula for the literal shifted summand's
cancelled polynomial witness. -/
lemma term_log_formula (n h l s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    eulerLog z (termNum n h l s)-eulerLog z (termDen n h l s) =
      (4*(l*n+s)+1:ℕ)*z^(4*s+1)/(1+z^(4*s+1)) - z/(1+z) + (l*n+s:ℕ) +
      3*((eulerLog z (coreNum n h l)-eulerLog z (coreDen n h l))+
        (eulerLog z (shiftedNum n l s)-eulerLog z (shiftedDen n l s))) := by
  have hA := coreNum_aeval_ne_zero n h l hh hz
  have hB := coreDen_aeval_ne_zero n h l hh hz
  have hC := shiftedNum_aeval_ne_zero n h l s hh hs hz
  have ho : Odd n := ⟨h, by omega⟩
  have hD := shiftedDen_aeval_ne_zero n l s ho (by omega) hz
  have hplus : aeval z (1+X^(4*(l*n+s)+1):ℚ[X])≠0 := by
    simpa using one_add_root_pow_ne_zero ho hz (4*(l*n+s)+1)
  have hX : aeval z (X^(l*n+s):ℚ[X])≠0 := by
    simpa using pow_ne_zero (l*n+s) (hz.ne_zero (by omega))
  have hdenplus : aeval z (1+X:ℚ[X])≠0 := by
    simpa only [map_add, map_one, aeval_X, pow_one] using one_add_root_pow_ne_zero ho hz 1
  have hAC : aeval z (coreNum n h l*shiftedNum n l s)≠0 := by simpa only [map_mul] using mul_ne_zero hA hC
  have hBD : aeval z (coreDen n h l*shiftedDen n l s)≠0 := by simpa only [map_mul] using mul_ne_zero hB hD
  unfold termNum termDen
  rw [eulerLog_mul _ _ _ (by simpa only [map_mul] using mul_ne_zero hplus hX)
    (by simpa only [map_pow] using pow_ne_zero 3 hAC),
    eulerLog_mul _ _ _ hplus hX, eulerLog_pow _ hAC,
    eulerLog_mul _ _ _ hdenplus (by simpa only [map_pow] using pow_ne_zero 3 hBD),
    eulerLog_pow _ hBD, eulerLog_mul _ _ _ hA hC, eulerLog_mul _ _ _ hB hD,
    eulerLog_monomial _ (hz.ne_zero (by omega)), eulerLog_plus,
    show (1+X:ℚ[X])=1+X^1 by simp, eulerLog_plus]
  rw [show 4*(l*n+s)+1=4*(l*n)+(4*s+1) by ring, block_pow n l _ hz.pow_eq_one]
  norm_num only [pow_one, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The complete first-order logarithmic error in formula (4) of the proof.
No derivative-bookkeeping hypothesis is present. -/
theorem term_log_shift_error (n h l s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    (eulerLog z (termNum n h l s)-eulerLog z (termDen n h l s)) -
      (eulerLog z (termNum n h 0 s)-eulerLog z (termDen n h 0 s)) =
      (l:K)*(3*(-(n:K)^2-4*(n:K)*halfHarmonic z h)+(n:K)+4*(n:K)*shiftL z s) := by
  rw [term_log_formula n h l s hh hs hz, term_log_formula n h 0 s hh hs hz,
    core_log_derivative n h l hh hz, core_log_derivative n h 0 hh hz]
  have he := shifted_log_derivative n h l s hh hs hz
  simp [shiftedNum, shiftedDen] at he ⊢
  unfold shiftL
  linear_combination 3*he

end Roots
end
end Guo62
```

### `GuoDeformation.lean`

```lean
import GuoSameJet
import GuoDixonUnits
import GuoTermWitness

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma quadratic_pair_sameJet (n a : ℕ) (hn : 0<n) (hz : IsPrimitiveRoot z n) :
    SameJet z ((1-q^((a:ℤ)-2*(n:ℤ)))*(1-q^((a:ℤ)+2*(n:ℤ))))
      ((1-q^a)^2) ((1-z^a)^2) := by
  have hz0 := hz.ne_zero hn.ne'
  have hz2 : z^((2:ℤ)*(n:ℤ))=1 := by
    rw [show (2:ℤ)*(n:ℤ)=((n*2:ℕ):ℤ) by omega, zpow_natCast, pow_mul,
      hz.pow_eq_one, one_pow]
  have hm : z^((a:ℤ)-2*(n:ℤ))=z^a := by rw [zpow_sub₀ hz0, hz2, zpow_natCast, div_one]
  have hp : z^((a:ℤ)+2*(n:ℤ))=z^a := by rw [zpow_add₀ hz0, hz2, zpow_natCast, mul_one]
  have hmj := (HasJet.const (z := z) 1).sub (HasJet.qzpow hz0 ((a:ℤ)-2*(n:ℤ)))
  have hpj := (HasJet.const (z := z) 1).sub (HasJet.qzpow hz0 ((a:ℤ)+2*(n:ℤ)))
  simp only [map_one, hm, hp, zero_sub] at hmj hpj
  have hb := (HasJet.const (z := z) 1).sub (HasJet.qpow (z := z) a)
  simp only [map_one, zero_sub] at hb
  refine ⟨-2*(a:K)*z^a*(1-z^a), ?_, ?_⟩
  · convert hmj.mul hpj using 1 <;> push_cast <;> ring
  · convert hb.mul hb using 1 <;> ring

lemma poch_pair_sameJet (n a k : ℕ) (hn : 0<n) (hz : IsPrimitiveRoot z n) :
    SameJet z (pochZ ((a:ℤ)-2*(n:ℤ)) 4 k * pochZ ((a:ℤ)+2*(n:ℤ)) 4 k)
      ((poch a 4 k)^2) ((aeval z (pochPoly a 4 k))^2) := by
  have hj := SameJet.prod (Finset.range k)
    (fun j => (1-q^(((a+4*j:ℕ):ℤ)-2*(n:ℤ)))*(1-q^(((a+4*j:ℕ):ℤ)+2*(n:ℤ))))
    (fun j => (1-q^(a+4*j))^2) (fun j => (1-z^(a+4*j))^2)
    (fun j _ => quadratic_pair_sameJet n (a+4*j) hn hz)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow] at hj
  convert hj using 1
  · unfold pochZ
    congr 1 <;> apply Finset.prod_congr rfl <;> intro j hj <;> congr 2 <;> push_cast <;> ring
  · rfl
  · rw [pochPoly_aeval]

/-- Actual terminating summands and original summands have identical first jets. -/
theorem terminatingTerm_sameJet (n h k : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (hk : k≤h) (hz : IsPrimitiveRoot z n) :
    ∃ v, SameJet z (terminatingTerm h k) (term k) v := by
  have hq := HasJet.qpow (z := z) (4*k+1)
  have hw := (HasJet.const (z := z) 1).add hq
  have hd := (HasJet.const (z := z) 1).add (HasJet.qpow (z := z) 1)
  have hden : 1+z≠0 := by simpa using one_add_root_pow_ne_zero (show Odd n from ⟨h,hh⟩) hz 1
  have hweight := (hw.div hd (by simpa using hden)).mul (HasJet.qpow (z := z) k)
  have h2 := HasJet.poly (z := z) (pochPoly 2 4 k)
  have h4 := HasJet.poly (z := z) (pochPoly 4 4 k)
  rw [show embed (pochPoly 2 4 k)=poch 2 4 k from pochPoly_map _ _ _] at h2
  rw [show embed (pochPoly 4 4 k)=poch 4 4 k from pochPoly_map _ _ _] at h4
  have hnum := (SameJet.refl h2).mul (poch_pair_sameJet n 2 k hn hz)
  have hdenj := (SameJet.refl h4).mul (poch_pair_sameJet n 4 k hn hz)
  have hunit : aeval z (pochPoly 4 4 k)≠0 := by
    rw [pochPoly_aeval]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simpa only [show 4+4*j=4*(j+1) by omega, pow_mul] using
      one_sub_root_pow_ne_zero (fourth_power_primitive (show Odd n from ⟨h,hh⟩) hz)
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : j+1<n))
  have hrat := hnum.div hdenj (mul_ne_zero hunit (pow_ne_zero 2 hunit))
  have htotal := (SameJet.refl hweight).mul hrat
  refine ⟨((1+z^(4*k+1))/(1+z)*z^k) *
    (aeval z (pochPoly 2 4 k))^3/(aeval z (pochPoly 4 4 k))^3, ?_⟩
  simp only [map_one,pow_one] at htotal
  convert htotal using 1
  · unfold terminatingTerm
    rw [show -4*(h:ℤ)=2-2*(n:ℤ) by omega,
      show 4*(h:ℤ)+4=2+2*(n:ℤ) by omega,
      show 2-4*(h:ℤ)=4-2*(n:ℤ) by omega,
      show 4*(h:ℤ)+6=4+2*(n:ℤ) by omega, ← pochZ_nat 2 4 k, ← pochZ_nat 4 4 k]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · unfold term
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · ring

end
end Guo62
```

### `GuoDixonSpecialize.lean`

```lean
import GuoDixonUnits
import GuoReciprocityAtOne
import GuoDixonRecurrence
import GuoDixonTermStep

namespace Guo62
noncomputable section

lemma q_pow_sub_ne_zero (a b : ℕ) (h : a≠b) : q^a-q^b≠0 :=
  sub_ne_zero.mpr (fun he => h (q_pow_injective he))

lemma q_div_pow (a b : ℕ) : q^a/q^b=q^((a:ℤ)-(b:ℤ)) := by
  rw [zpow_sub₀ (show q≠0 from RatFunc.X_ne_zero),zpow_natCast,zpow_natCast]

lemma dixon_param_units (N k : ℕ) :
    paramPoch (q^4) (q^4) k≠0 ∧
    paramPoch (q^2/q^(4*N)) (q^4) k≠0 ∧
    paramPoch (q^6*q^(4*N)) (q^4) k≠0 := by
  have hd := terminating_denominators N k
  rw [pochZ_param,pochZ_param,pochZ_param] at hd
  refine ⟨hd.1, ?_, ?_⟩
  · convert hd.2.1 using 1
    rw [q_div_pow]
    congr 2
  · convert hd.2.2 using 1
    rw [← pow_add,show 6+4*N=4*N+6 by omega]
    simp only [show 4*(N:ℤ)+6=((4*N+6:ℕ):ℤ) by omega,zpow_natCast]

lemma source_dixon_term_step (N k : ℕ) :
    terminatingTerm N (k+1) =
      terminatingTerm N k * dixonT q (q^(4*N)) (q^(4*k)) := by
  rw [terminatingTerm_dixon,terminatingTerm_dixon]
  have hd := dixon_param_units N k
  apply dixon_term_step q (q^(4*N)) k (q_pow_ne_zero _) one_add_q_ne_zero
  · simpa only [← pow_succ'] using one_add_q_pow_ne_zero (4*k+1)
  · rw [← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [← pow_add]
    exact q_pow_sub_ne_zero _ _ (by omega)
  · rw [← pow_add,← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · exact hd.1
  · exact hd.2.1
  · exact hd.2.2

lemma source_dixon_parameter_step (N k : ℕ) (hN : 0<N) :
    dixonRate q (q^(4*N)) * terminatingTerm (N-1) k =
      terminatingTerm N k * dixonV q (q^(4*N)) (q^(4*k)) := by
  rw [terminatingTerm_dixon,terminatingTerm_dixon]
  have hd := dixon_param_units N k
  have hprev : q^(4*(N-1))=q^(4*N)/q^4 := by
    apply (eq_div_iff (q_pow_ne_zero 4)).mpr
    rw [← pow_add]
    congr 1
    omega
  rw [hprev]
  apply dixon_parameter_step q (q^(4*N)) k RatFunc.X_ne_zero (q_pow_ne_zero _)
  · exact one_sub_inv_ne_zero _ (one_sub_q_pow_ne_zero (by omega))
  · rw [← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [q_div_pow]
    exact one_sub_q_zpow_ne_zero _ (by omega)
  · rw [← pow_add,← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [q_div_pow]
    exact one_sub_q_zpow_ne_zero _ (by omega)
  · rw [← pow_succ']
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [← pow_add]
    exact q_pow_sub_ne_zero _ _ (by omega)
  · exact one_add_q_ne_zero
  · exact hd.1
  · simpa only [pow_zero] using q_pow_sub_ne_zero (4*N) 0 (by omega)
  · exact q_pow_sub_ne_zero _ _ (by omega)
  · exact hd.2.1
  · exact hd.2.2

lemma source_dixon_certificate (N k : ℕ) (hN : 0<N) :
    dixonT q (q^(4*N)) (q^(4*k)) * dixonR q (q^(4*N)) (q^4*q^(4*k)) -
      dixonR q (q^(4*N)) (q^(4*k)) = 1-dixonV q (q^(4*N)) (q^(4*k)) := by
  apply dixon_certificate
  · rw [← pow_succ']
    simpa only [pow_zero] using q_pow_sub_ne_zero (4*N+1) 0 (by omega)
  · simpa only [← pow_succ'] using one_add_q_pow_ne_zero (4*k+1)
  · rw [← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [← pow_add]
    exact q_pow_sub_ne_zero _ _ (by omega)
  · rw [← pow_add]
    exact one_add_q_pow_ne_zero _
  · rw [← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [← pow_add,← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)
  · rw [← pow_add,← pow_add]
    exact one_sub_q_pow_ne_zero (by omega)

end
end Guo62
```

### `GuoTail.lean`

```lean
import GuoTermWitness

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma shiftedNum_tail_zero (n h l s : ℕ) (hh : n=2*h+1) (hs : h<s)
    (hz : z^n=1) : aeval z (shiftedNum n l s)=0 := by
  rw [shiftedNum, pochPoly_aeval]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hs)
  rw [show 4*(l*n)+2+4*h=n*(4*l+2) by rw [hh]; ring,
    pow_mul, hz, one_pow, sub_self]

/-- The cubic numerator makes every tail term invisible to the first jet.
The proof differentiates only the outer cube, not the prefix product. -/
theorem term_tail_jet_zero (n h l s : ℕ) (hh : n=2*h+1) (hs : h<s)
    (hz : z^n=1) :
    aeval z (termNum n h l s)=0 ∧ aeval z (termNum n h l s).derivative=0 := by
  have he := shiftedNum_tail_zero n h l s hh hs hz
  constructor
  · simp only [termNum, map_mul, map_pow, he, mul_zero, zero_pow (by decide : 3≠0)]
  · simp only [termNum, derivative_mul, derivative_pow, map_add, map_mul, map_pow,
      he, mul_zero, zero_pow (by decide : 3≠0), zero_pow (by decide : 2≠0), zero_add, zero_mul]

/-- Tail congruence for the actual rational summand, including regularity. -/
theorem source_tail_congSq_root (n h l s : ℕ) (hn : 0<n) (hh : n=2*h+1)
    (hs : h<s) (hsn : s<n) (hz : IsPrimitiveRoot z n) :
    CongSq n (term (l*n+s)) 0 := by
  rw [term_fraction_identity n h l s hn hh]
  have hB := termDen_aeval_ne_zero n h l s hh hsn hz
  have hBn : termDen n h l s≠0 := by intro he; exact hB (by rw [he, map_zero])
  have hBc := coprime_cyclotomic_of_aeval_ne_zero hn hz _ hB
  have hv := term_tail_jet_zero n h l s hh hs hz.pow_eq_one
  have hd := cyclotomic_square_dvd_of_aeval_zero hn hz _ hv.1 hv.2
  have hd' : (cyclotomic n ℚ)^2 ∣ termNum n h l s*1-0*termDen n h l s := by
    simpa only [mul_one, zero_mul, sub_zero] using hd
  have hc := (congSq_fractions_iff n _ _ 0 1 hBn one_ne_zero hBc isCoprime_one_right).mpr hd'
  simpa only [map_zero, zero_div] using hc


end
end Guo62
```

### `GuoDixonSum.lean`

```lean
import GuoDixonSpecialize

namespace Guo62
noncomputable section

lemma dixon_telescope (N k : ℕ) (hN : 0<N) :
    terminatingTerm N (k+1) * dixonR q (q^(4*N)) (q^(4*(k+1))) -
      terminatingTerm N k * dixonR q (q^(4*N)) (q^(4*k)) =
    terminatingTerm N k - dixonRate q (q^(4*N)) * terminatingTerm (N-1) k := by
  rw [source_dixon_term_step]
  have hpow : q^(4*(k+1))=q^4*q^(4*k) := by rw [← pow_add]; congr 1; omega
  rw [hpow]
  have hc := source_dixon_certificate N k hN
  have hp := source_dixon_parameter_step N k hN
  linear_combination (terminatingTerm N k)*hc + hp

lemma sum_telescope {K : Type*} [AddCommGroup K] (G : ℕ → K) (r : ℕ) :
    (∑ k ∈ Finset.range r, (G (k+1)-G k)) = G r-G 0 := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ,ih]; abel

lemma dixon_sum_recurrence (N : ℕ) :
    (∑ k ∈ Finset.range (N+2), terminatingTerm (N+1) k) =
      dixonRate q (q^(4*(N+1))) * ∑ k ∈ Finset.range (N+1), terminatingTerm N k := by
  have hl := fun k => dixon_telescope (N+1) k (by omega)
  have hs := Finset.sum_congr (s₁ := Finset.range (N+2)) rfl (fun k _ => hl k)
  rw [sum_telescope (fun k => terminatingTerm (N+1) k *
    dixonR q (q^(4*(N+1))) (q^(4*k))) (N+2),
    Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hbottom : dixonR q (q^(4*(N+1))) 1=0 := by simp [dixonR]
  have htop := terminatingTerm_zero (N+1) (N+2) (by omega)
  simp only [htop, zero_mul,pow_zero,hbottom,mul_zero,sub_self] at hs
  have hp : (∑ k ∈ Finset.range (N+2), terminatingTerm N k) =
      ∑ k ∈ Finset.range (N+1), terminatingTerm N k := by
    rw [show N+2=(N+1)+1 by omega,Finset.sum_range_succ,
      terminatingTerm_zero N (N+1) (by omega),add_zero]
  simp only [Nat.add_sub_cancel] at hs
  rw [hp] at hs
  exact (sub_eq_zero.mp hs.symm)

def dixonClosed (N : ℕ) : RatFunc ℚ :=
  (q^N)⁻¹ * ((1-q^(4*N+2))/(1-q^2)) * poch 3 4 N / poch 5 4 N

lemma dixon_rate_succ (N : ℕ) :
    dixonRate q (q^(4*(N+1))) = q⁻¹ *
      ((1-q^(4*N+6))/(1-q^(4*N+2))) * ((1-q^(4*N+3))/(1-q^(4*N+5))) := by
  unfold dixonRate
  have h1 : q^2*q^(4*(N+1))=q^(4*N+6) := by rw [← pow_add]; congr 1; omega
  have h2 : q^(4*(N+1))/q^2=q^(4*N+2) := by
    apply (div_eq_iff (q_pow_ne_zero _)).mpr
    rw [← pow_add]
    congr 1
  have h3 : q^(4*(N+1))/q=q^(4*N+3) := by
    apply (div_eq_iff (show q≠0 from RatFunc.X_ne_zero)).mpr
    rw [← pow_succ]
    congr 1
  have h4 : q*q^(4*(N+1))=q^(4*N+5) := by
    rw [← pow_succ']
    congr 1
  rw [h1,h2,h3,h4]
  ring

lemma dixon_closed_recurrence (N : ℕ) :
    dixonClosed (N+1)=dixonRate q (q^(4*(N+1)))*dixonClosed N := by
  rw [dixon_rate_succ]
  unfold dixonClosed
  have hp (a : ℕ) : poch a 4 (N+1)=poch a 4 N*(1-q^(a+4*N)) :=
    Finset.prod_range_succ _ _
  rw [hp,hp,pow_succ]
  rw [show 4*(N+1)+2=4*N+6 by omega,
    show 3+4*N=4*N+3 by omega,show 5+4*N=4*N+5 by omega]
  field_simp [q_pow_ne_zero N, RatFunc.X_ne_zero,
    one_sub_q_pow_ne_zero (by omega : 0<4*N+2),
    one_sub_q_pow_ne_zero (by omega : 0<4*N+5),poch_ne_zero (by decide : 0<5) 4 N]

/-- Finite Dixon identity, with both telescoping boundaries proved. -/
theorem finite_dixon_sum (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), terminatingTerm N k) =
      (q^N)⁻¹ * ((1-q^(4*N+2))/(1-q^2)) * poch 3 4 N / poch 5 4 N := by
  change (∑ k ∈ Finset.range (N+1), terminatingTerm N k)=dixonClosed N
  induction N with
  | zero => simp [dixonClosed,poch,terminatingTerm_at_zero,one_sub_q_pow_ne_zero (by decide : 0<2)]
  | succ N ih => rw [show N+1+1=N+2 by omega,dixon_sum_recurrence,ih,dixon_closed_recurrence]

end
end Guo62
```

### `GuoTermJet.lean`

```lean
import GuoTail

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def termValue (z : K) (n h l s : ℕ) : K :=
  aeval z (termNum n h l s) / aeval z (termDen n h l s)

def termEuler (z : K) (n h l s : ℕ) : K :=
  z * (aeval z (termNum n h l s).derivative * aeval z (termDen n h l s) -
    aeval z (termNum n h l s) * aeval z (termDen n h l s).derivative) /
      (aeval z (termDen n h l s))^2

lemma term_value_factor (z : K) (n h l s : ℕ) :
    termValue z n h l s = (1+z^(4*(l*n+s)+1))/(1+z)*z^(l*n+s)*
      ((aeval z (coreNum n h l)/aeval z (coreDen n h l)) *
        (aeval z (shiftedNum n l s)/aeval z (shiftedDen n l s)))^3 := by
  simp only [termValue, termNum, termDen, map_mul, map_pow, map_add, map_one, aeval_X,
    div_eq_mul_inv, mul_inv_rev, mul_pow]
  ring

/-- Source formula (3), for the actual regular summand witnesses. -/
theorem term_value_shift (z : K) (n h l s : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    termValue z n h l s =
      (algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 * termValue z n h 0 s := by
  obtain ⟨hA, hB⟩ := shifted_values n l s hz.pow_eq_one
  rw [term_value_factor, term_value_factor, core_value n h l hh hz, core_value n h 0 hh hz,
    hA, hB]
  have hp : z^(l*n+s)=z^s := by
    rw [pow_add, Nat.mul_comm l n, pow_mul, hz.pow_eq_one, one_pow, one_mul]
  rw [hp, show 4*(l*n+s)+1=4*(l*n)+(4*s+1) by ring, block_pow n l _ hz.pow_eq_one]
  simp [shiftedNum, shiftedDen, halfPoch]
  ring

lemma term_euler_eq_value_log (z : K) (n h l s : ℕ) (hh : n=2*h+1)
    (hs : s≤h) (hz : IsPrimitiveRoot z n) :
    termEuler z n h l s = termValue z n h l s *
      (eulerLog z (termNum n h l s)-eulerLog z (termDen n h l s)) := by
  exact quotient_euler_cross z _ _ (termNum_aeval_ne_zero n h l s hh hs hz)
    (termDen_aeval_ne_zero n h l s hh (by omega) hz)

/-- Source formula (4) with no bookkeeping or value-scaling hypotheses.
Both sides use the polynomial witnesses proved equal to literal term(l*n+s). -/
theorem term_euler_shift_error (z : K) (n h l s : ℕ) (hh : n=2*h+1) (hs : s≤h)
    (hz : IsPrimitiveRoot z n) :
    termEuler z n h l s = (algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 *
      (termEuler z n h 0 s + (l:K)*termValue z n h 0 s *
        (3*(-(n:K)^2-4*(n:K)*halfHarmonic z h)+(n:K)+4*(n:K)*shiftL z s)) := by
  rw [term_euler_eq_value_log z n h l s hh hs hz,
    term_euler_eq_value_log z n h 0 s hh hs hz, term_value_shift z n h l s hh hz]
  have he := term_log_shift_error n h l s hh hs hz
  linear_combination (algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 * termValue z n h 0 s * he

end
end Guo62
```

### `GuoBlockBridge.lean`

```lean
import GuoTermJet
import GuoReciprocityAtOne
import GuoJet

namespace Guo62
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K}

lemma base_term_value_bridge (n h s : ℕ) (hh : n=2*h+1)
    (hz : IsPrimitiveRoot z n) :
    termValue z n h 0 s = shiftTerm z (z^4) 1 h s := by
  have hn : 0<n := by omega
  have hz0 := hz.ne_zero hn.ne'
  have hr := (root_half_relations hn hz h hh).1
  have hprod : aeval z (pochPoly 2 4 s) / aeval z (pochPoly 4 4 s) =
      shiftRatio (z^4) 1 h s := by
    rw [pochPoly_aeval, pochPoly_aeval, ← Finset.prod_div_distrib]
    unfold shiftRatio prefixProd
    apply Finset.prod_congr rfl
    intro j _
    have ha : z^(2+4*j) = (z^4)^((j:ℤ)-(h:ℤ)) := by
      rw [zpow_sub₀ (pow_ne_zero 4 hz0), zpow_natCast, div_eq_mul_inv, zpow_natCast, hr, inv_inv,
        pow_add, pow_mul]
      ring
    have hb : z^(4+4*j) = (z^4)^((j:ℤ)+1) := by
      rw [show (j:ℤ)+1=((j+1:ℕ):ℤ) by omega, zpow_natCast, ← pow_mul]
      congr 1
      omega
    rw [ha, hb]
    simp
  rw [term_value_factor, core_value n h 0 hh hz]
  simp only [halfPoch, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
    Nat.cast_one, div_one, map_one, one_mul, Nat.zero_mul, Nat.zero_add,
    shiftedNum, shiftedDen]
  rw [hprod]
  unfold shiftTerm
  rw [show z^(4*s+1)=z*(z^4)^s by rw [pow_add, pow_one, pow_mul]; ring]
  simp

lemma term_hasJet (n h l s : ℕ) (hn : 0<n) (hh : n=2*h+1) (hs : s<n)
    (hz : IsPrimitiveRoot z n) :
    HasJet z (term (l*n+s)) (termValue z n h l s) (termEuler z n h l s) := by
  rw [term_fraction_identity n h l s hn hh]
  exact HasJet.fraction _ _ (termDen_aeval_ne_zero n h l s hh hs hz)

lemma block_jet_values (n h l : ℕ) (hn : 0<n) (hh : n=2*h+1) (he : Even h)
    (hz : IsPrimitiveRoot z n) :
    (∑ s ∈ Finset.range n, termValue z n h l s) =
      (algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 *
        ∑ s ∈ Finset.range n, termValue z n h 0 s ∧
    (∑ s ∈ Finset.range n, termEuler z n h l s) =
      (algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 *
        ∑ s ∈ Finset.range n, termEuler z n h 0 s := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => term_value_shift z n h l s hh hz)
  · have herr := source_shift_error_zero n h hn hh he hz
    simp_rw [← base_term_value_bridge n h _ hh hz] at herr
    have heq : ∀ s<n, termEuler z n h l s =
        (algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 *
        (termEuler z n h 0 s + (l:K)*termValue z n h 0 s *
          (3*(-(n:K)^2-4*(n:K)*halfHarmonic z h)+(n:K)+4*(n:K)*shiftL z s)) := by
      intro s hs
      by_cases hsh : s≤h
      · exact term_euler_shift_error z n h l s hh hsh hz
      · have ht := term_tail_jet_zero n h l s hh (by omega) hz.pow_eq_one
        have ht0 := term_tail_jet_zero n h 0 s hh (by omega) hz.pow_eq_one
        simp only [termEuler, termValue, ht.1, ht.2, ht0.1, ht0.2,
          mul_zero, zero_mul, sub_zero, zero_div, zero_add]
    have herrn : (∑ s ∈ Finset.range n, termValue z n h 0 s *
        (3*(-(n:K)^2-4*(n:K)*halfHarmonic z h)+(n:K)+4*(n:K)*shiftL z s)) = 0 := by
      rw [← herr]
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : h+1≤n))
      intro s hs hsn
      have ht := (term_tail_jet_zero n h 0 s hh (by simpa using hsn) hz.pow_eq_one).1
      simp [termValue, ht]
    calc
      _ = ∑ s ∈ Finset.range n,
          ((algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 * termEuler z n h 0 s +
          ((algebraMap ℚ K (halfPoch l/(Nat.factorial l:ℚ)))^3 * (l:K)) *
          (termValue z n h 0 s *
          (3*(-(n:K)^2-4*(n:K)*halfHarmonic z h)+(n:K)+4*(n:K)*shiftL z s))) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [heq s (Finset.mem_range.mp hs)]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, herrn]
        ring

/-- The full block lifting, including reduced-denominator regularity. -/
theorem source_block_lift (l n : ℕ) (hn : 1<n) (h4 : n%4=1) :
    CongSq n (∑ s ∈ Finset.range n, term (l*n+s))
      (algebraMap ℚ (RatFunc ℚ) ((halfPoch l/(Nat.factorial l:ℚ))^3) *
        ∑ s ∈ Finset.range n, term s) := by
  let z := Complex.exp (2*Real.pi*Complex.I/n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n (by omega)
  obtain ⟨hh, he⟩ := admissible_half n hn h4
  let h := (n-1)/2
  have hhalf : n=2*h+1 := by dsimp [h]; omega
  obtain ⟨hv,hd⟩ := block_jet_values n h l (by omega) hhalf he.1 hz
  have hsum := HasJet.sum (Finset.range n) (fun s => term (l*n+s))
    (fun s => termValue z n h l s) (fun s => termEuler z n h l s)
    (fun s hs => term_hasJet n h l s (by omega) hhalf (Finset.mem_range.mp hs) hz)
  have hsum0 := HasJet.sum (Finset.range n) (fun s => term s)
    (fun s => termValue z n h 0 s) (fun s => termEuler z n h 0 s)
    (fun s hs => by simpa using term_hasJet n h 0 s (by omega) hhalf (Finset.mem_range.mp hs) hz)
  have hscaled := (HasJet.const (z := z) ((halfPoch l/(Nat.factorial l:ℚ))^3)).mul hsum0
  simp only [map_pow, zero_mul, zero_add] at hscaled
  rw [hv,hd] at hsum
  simpa only [map_pow] using hsum.congSq (by omega) hz hscaled

end
end Guo62
```

### `GuoStage2Audit.lean`

```lean
import GuoAudit
import GuoTermJet
import GuoReciprocityAtOne

#eval Lean.versionString
#print Guo62.eulerLog
#print Guo62.blockNum
#print Guo62.blockDen
#print Guo62.coreNum
#print Guo62.coreDen
#print Guo62.halfHarmonic
#print Guo62.shiftH
#print Guo62.shiftL
#print Guo62.term
#print Guo62.termNum
#print Guo62.termDen
#print Guo62.termValue
#print Guo62.termEuler
#check Guo62.eulerLog_pochPoly
#print axioms Guo62.eulerLog_pochPoly
#check Guo62.block_pair_values
#print axioms Guo62.block_pair_values
#check Guo62.block_value
#print axioms Guo62.block_value
#check Guo62.block_log_derivative
#print axioms Guo62.block_log_derivative
#check Guo62.poch_one
#print axioms Guo62.poch_one
#check Guo62.poch_split_middle
#print axioms Guo62.poch_split_middle
#check Guo62.poch_split_last
#print axioms Guo62.poch_split_last
#check Guo62.block_fraction_identity
#print axioms Guo62.block_fraction_identity
#check Guo62.block_pow
#print axioms Guo62.block_pow
#check Guo62.low_residue
#print axioms Guo62.low_residue
#check Guo62.high_residue
#print axioms Guo62.high_residue
#check Guo62.denominator_residue_low
#print axioms Guo62.denominator_residue_low
#check Guo62.denominator_residue_high
#print axioms Guo62.denominator_residue_high
#check Guo62.block_residue_units
#print axioms Guo62.block_residue_units
#check Guo62.pochPoly_aeval
#print axioms Guo62.pochPoly_aeval
#check Guo62.blockDen_aeval_ne_zero
#print axioms Guo62.blockDen_aeval_ne_zero
#check Guo62.blockNum_aeval_ne_zero
#print axioms Guo62.blockNum_aeval_ne_zero
#check Guo62.block_fraction_regular
#print axioms Guo62.block_fraction_regular
#check Guo62.poch_blocks
#print axioms Guo62.poch_blocks
#check Guo62.core_fraction_identity
#print axioms Guo62.core_fraction_identity
#check Guo62.half_ratio_product
#print axioms Guo62.half_ratio_product
#check Guo62.coreNum_aeval_ne_zero
#print axioms Guo62.coreNum_aeval_ne_zero
#check Guo62.coreDen_aeval_ne_zero
#print axioms Guo62.coreDen_aeval_ne_zero
#check Guo62.core_regular
#print axioms Guo62.core_regular
#check Guo62.core_value
#print axioms Guo62.core_value
#check Guo62.core_log_derivative
#print axioms Guo62.core_log_derivative
#check Guo62.core_euler_derivative
#print axioms Guo62.core_euler_derivative
#check Guo62.fraction_cross_derivative_zero
#print axioms Guo62.fraction_cross_derivative_zero
#check Guo62.rootFrac_inv
#print axioms Guo62.rootFrac_inv
#check Guo62.upper_residue_inverse
#print axioms Guo62.upper_residue_inverse
#check Guo62.upper_harmonic
#print axioms Guo62.upper_harmonic
#check Guo62.eulerLog_one
#print axioms Guo62.eulerLog_one
#check Guo62.eulerLog_mul
#print axioms Guo62.eulerLog_mul
#check Guo62.eulerLog_prod
#print axioms Guo62.eulerLog_prod
#check Guo62.eulerLog_binomial
#print axioms Guo62.eulerLog_binomial
#check Guo62.eulerLog_geom
#print axioms Guo62.eulerLog_geom
#check Guo62.quotient_euler_cross
#print axioms Guo62.quotient_euler_cross
#check Guo62.one_sub_inv_ne_zero
#print axioms Guo62.one_sub_inv_ne_zero
#check Guo62.shiftRatio_one_ne_zero
#print axioms Guo62.shiftRatio_one_ne_zero
#check Guo62.shiftTerm_one_ne_zero
#print axioms Guo62.shiftTerm_one_ne_zero
#check Guo62.reciprocity_prefactor_one
#print axioms Guo62.reciprocity_prefactor_one
#check Guo62.shiftTerm_one_reflection
#print axioms Guo62.shiftTerm_one_reflection
#check Guo62.source_shift_error_zero
#print axioms Guo62.source_shift_error_zero
#check Guo62.Regular.pow
#print axioms Guo62.Regular.pow
#check Guo62.ratio_split
#print axioms Guo62.ratio_split
#check Guo62.term_factorization
#print axioms Guo62.term_factorization
#check Guo62.source_ratio_regular_root
#print axioms Guo62.source_ratio_regular_root
#check Guo62.source_term_regular_root
#print axioms Guo62.source_term_regular_root
#check Guo62.source_term_regular
#print axioms Guo62.source_term_regular
#check Guo62.source_lhs_regular
#print axioms Guo62.source_lhs_regular
#check Guo62.shiftedDen_aeval_ne_zero
#print axioms Guo62.shiftedDen_aeval_ne_zero
#check Guo62.shiftedNum_aeval_ne_zero
#print axioms Guo62.shiftedNum_aeval_ne_zero
#check Guo62.shifted_values
#print axioms Guo62.shifted_values
#check Guo62.shifted_log_derivative
#print axioms Guo62.shifted_log_derivative
#check Guo62.sum_reverse_tail
#print axioms Guo62.sum_reverse_tail
#check Guo62.shiftH_formula
#print axioms Guo62.shiftH_formula
#check Guo62.shiftH_reflection
#print axioms Guo62.shiftH_reflection
#check Guo62.plus_weight_reflection
#print axioms Guo62.plus_weight_reflection
#check Guo62.shiftL_reflection
#print axioms Guo62.shiftL_reflection
#check Guo62.shiftedNum_tail_zero
#print axioms Guo62.shiftedNum_tail_zero
#check Guo62.term_tail_jet_zero
#print axioms Guo62.term_tail_jet_zero
#check Guo62.source_tail_congSq_root
#print axioms Guo62.source_tail_congSq_root
#check Guo62.term_value_factor
#print axioms Guo62.term_value_factor
#check Guo62.term_value_shift
#print axioms Guo62.term_value_shift
#check Guo62.term_euler_eq_value_log
#print axioms Guo62.term_euler_eq_value_log
#check Guo62.term_euler_shift_error
#print axioms Guo62.term_euler_shift_error
#check Guo62.term_fraction_identity
#print axioms Guo62.term_fraction_identity
#check Guo62.eulerLog_pow
#print axioms Guo62.eulerLog_pow
#check Guo62.eulerLog_monomial
#print axioms Guo62.eulerLog_monomial
#check Guo62.eulerLog_plus
#print axioms Guo62.eulerLog_plus
#check Guo62.termDen_aeval_ne_zero
#print axioms Guo62.termDen_aeval_ne_zero
#check Guo62.termNum_aeval_ne_zero
#print axioms Guo62.termNum_aeval_ne_zero
#check Guo62.term_log_formula
#print axioms Guo62.term_log_formula
#check Guo62.term_log_shift_error
#print axioms Guo62.term_log_shift_error
```

### `GuoBlockSum.lean`

```lean
import GuoBlockBridge
import GuoCongSqAlgebra

namespace Guo62
noncomputable section

lemma sum_blocks {K : Type*} [AddCommMonoid K] (f : ℕ → K) (m n : ℕ) :
    (∑ k ∈ Finset.range (m*n), f k) =
      ∑ l ∈ Finset.range m, ∑ s ∈ Finset.range n, f (l*n+s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The arbitrary-m first-order lifting, before use of the finite base identity. -/
theorem source_all_blocks (m n : ℕ) (hn : 1<n) (h4 : n%4=1) :
    CongSq n (lhs m n)
      (lhs 1 n * algebraMap ℚ (RatFunc ℚ)
        (∑ l ∈ Finset.range m, halfPoch l^3/(Nat.factorial l:ℚ)^3)) := by
  have hc := CongSq.sum (Finset.range m)
    (fun l => ∑ s ∈ Finset.range n, term (l*n+s))
    (fun l => algebraMap ℚ (RatFunc ℚ) ((halfPoch l/(Nat.factorial l:ℚ))^3) *
      ∑ s ∈ Finset.range n, term s)
    (fun l _ => source_block_lift l n hn h4)
  have hsum : (∑ l ∈ Finset.range m,
      algebraMap ℚ (RatFunc ℚ) ((halfPoch l/(Nat.factorial l:ℚ))^3) *
      ∑ s ∈ Finset.range n, term s) =
      lhs 1 n * algebraMap ℚ (RatFunc ℚ)
        (∑ l ∈ Finset.range m, halfPoch l^3/(Nat.factorial l:ℚ)^3) := by
    rw [← Finset.sum_mul, ← map_sum]
    simp only [div_pow, lhs, one_mul, term]
    ring
  rw [hsum] at hc
  simpa only [lhs, term, sum_blocks] using hc

end
end Guo62
```

### `GuoBase.lean`

```lean
import GuoDixonSum
import GuoDeformation
import GuoBlockSum
import GuoRhsRegularity

namespace Guo62
noncomputable section

lemma rhs_one (n : ℕ) : rhs 1 n =
    qInt2 n * poch 3 4 ((n-1)/2) / poch 5 4 ((n-1)/2) * (q^((n-1)/2))⁻¹ := by
  simp [rhs,halfPoch]

/-- The base block is proved through finite Dixon, not assumed as a published link. -/
theorem source_base_block (n : ℕ) (hn : 1<n) (h4 : n%4=1) :
    CongSq n (lhs 1 n) (rhs 1 n) := by
  let h := (n-1)/2
  have hh : n=2*h+1 := by have := (admissible_half n hn h4).1; dsimp [h]; omega
  let z := Complex.exp (2*Real.pi*Complex.I/n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n (by omega)
  have hs : ∀ k∈Finset.range n, CongSq n (term k) (terminatingTerm h k) := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    by_cases hkh : k≤h
    · obtain ⟨v,hv⟩ := terminatingTerm_sameJet n h k (by omega) hh hkh hz
      exact (hv.congSq (by omega) hz).symm
    · rw [terminatingTerm_zero h k (by omega)]
      simpa only [Nat.zero_mul,Nat.zero_add] using
        source_tail_congSq_root n h 0 k (by omega) hh (by omega) hkn hz
  have hc := CongSq.sum (Finset.range n) term (terminatingTerm h) hs
  have heq : (∑ k ∈ Finset.range n, terminatingTerm h k) =
      ∑ k ∈ Finset.range (h+1), terminatingTerm h k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega : h+1≤n))
    intro k hk hkh
    exact terminatingTerm_zero h k (by simpa using hkh)
  rw [heq,finite_dixon_sum] at hc
  have hr : (q^h)⁻¹ * ((1-q^(4*h+2))/(1-q^2)) * poch 3 4 h / poch 5 4 h = rhs 1 n := by
    rw [rhs_one,qInt2_eq_fraction,show 4*h+2=2*n by omega]
    ring
  rw [hr] at hc
  simpa only [lhs,one_mul,term] using hc

end
end Guo62
```

### `GuoConjecture.lean`

```lean
import GuoBase

namespace Guo62
open Polynomial
noncomputable section

/-- Guo's Conjecture 6.2, with the fixed literal review endpoint. -/
theorem guo_conj_6_2 (m n : ℕ) (hm : 0 < m) (hn : 1 < n) (h4 : n % 4 = 1) :
  CongSq n
    (∑ k ∈ Finset.range (m*n), (1 + q^(4*k+1)) * (poch 2 4 k)^3 * q^k / ((1 + q) * (poch 4 4 k)^3))
    (qInt2 n * poch 3 4 ((n-1)/2) / poch 5 4 ((n-1)/2) * (q^((n-1)/2))⁻¹ *
      ((∑ k ∈ Finset.range m, (halfPoch k)^3 / (Nat.factorial k : ℚ)^3 : ℚ) : RatFunc ℚ)) := by
  change CongSq n (lhs m n) (rhs m n)
  let c : ℚ := ∑ k ∈ Finset.range m, (halfPoch k)^3/(Nat.factorial k:ℚ)^3
  have hs := CongSq.refl n (Regular.const (cyclotomic n ℚ) c)
  have hb := (source_base_block n hn h4).mul hs
  have ha := (source_all_blocks m n hn h4).trans hb
  have hr : rhs 1 n * algebraMap ℚ (RatFunc ℚ) c = rhs m n := by
    rw [rhs_one]
    rfl
  rw [hr] at ha
  have _ := endpoint_denominators_nonzero m n
  have _ := source_rhs_regular m n hm hn h4
  exact ha

#print guo_conj_6_2
#print axioms guo_conj_6_2
#print axioms endpoint_denominators_nonzero
end
end Guo62
```

### `GuoStage3Audit.lean`

```lean
import GuoConjecture
import GuoStage2Audit

#eval Lean.versionString
#check Guo62.rhs_one
#print axioms Guo62.rhs_one
#check Guo62.source_base_block
#print axioms Guo62.source_base_block
#check Guo62.base_term_value_bridge
#print axioms Guo62.base_term_value_bridge
#check Guo62.term_hasJet
#print axioms Guo62.term_hasJet
#check Guo62.block_jet_values
#print axioms Guo62.block_jet_values
#check Guo62.source_block_lift
#print axioms Guo62.source_block_lift
#check Guo62.sum_blocks
#print axioms Guo62.sum_blocks
#check Guo62.source_all_blocks
#print axioms Guo62.source_all_blocks
#check Guo62.CongSq.refl
#print axioms Guo62.CongSq.refl
#check Guo62.CongSq.symm
#print axioms Guo62.CongSq.symm
#check Guo62.CongSq.add
#print axioms Guo62.CongSq.add
#check Guo62.CongSq.trans
#print axioms Guo62.CongSq.trans
#check Guo62.CongSq.mul
#print axioms Guo62.CongSq.mul
#check Guo62.CongSq.sum
#print axioms Guo62.CongSq.sum
#check Guo62.Regular.const
#print axioms Guo62.Regular.const
#check Guo62.guo_conj_6_2
#print axioms Guo62.guo_conj_6_2
#check Guo62.quadratic_pair_sameJet
#print axioms Guo62.quadratic_pair_sameJet
#check Guo62.poch_pair_sameJet
#print axioms Guo62.poch_pair_sameJet
#check Guo62.terminatingTerm_sameJet
#print axioms Guo62.terminatingTerm_sameJet
#check Guo62.paramPoch_succ
#print axioms Guo62.paramPoch_succ
#check Guo62.paramPoch_shift
#print axioms Guo62.paramPoch_shift
#check Guo62.dixon_certificate
#print axioms Guo62.dixon_certificate
#check Guo62.paramPoch_shift_div
#print axioms Guo62.paramPoch_shift_div
#check Guo62.paramPoch_unshift_div
#print axioms Guo62.paramPoch_unshift_div
#check Guo62.dixon_parameter_step
#print axioms Guo62.dixon_parameter_step
#check Guo62.q_pow_sub_ne_zero
#print axioms Guo62.q_pow_sub_ne_zero
#check Guo62.q_div_pow
#print axioms Guo62.q_div_pow
#check Guo62.dixon_param_units
#print axioms Guo62.dixon_param_units
#check Guo62.source_dixon_term_step
#print axioms Guo62.source_dixon_term_step
#check Guo62.source_dixon_parameter_step
#print axioms Guo62.source_dixon_parameter_step
#check Guo62.source_dixon_certificate
#print axioms Guo62.source_dixon_certificate
#check Guo62.dixon_telescope
#print axioms Guo62.dixon_telescope
#check Guo62.sum_telescope
#print axioms Guo62.sum_telescope
#check Guo62.dixon_sum_recurrence
#print axioms Guo62.dixon_sum_recurrence
#check Guo62.dixon_rate_succ
#print axioms Guo62.dixon_rate_succ
#check Guo62.dixon_closed_recurrence
#print axioms Guo62.dixon_closed_recurrence
#check Guo62.finite_dixon_sum
#print axioms Guo62.finite_dixon_sum
#check Guo62.dixon_term_step
#print axioms Guo62.dixon_term_step
#check Guo62.q_pow_injective
#print axioms Guo62.q_pow_injective
#check Guo62.q_zpow_ne_one
#print axioms Guo62.q_zpow_ne_one
#check Guo62.one_sub_q_zpow_ne_zero
#print axioms Guo62.one_sub_q_zpow_ne_zero
#check Guo62.pochZ_param
#print axioms Guo62.pochZ_param
#check Guo62.pochZ_nat
#print axioms Guo62.pochZ_nat
#check Guo62.pochZ_ne_zero
#print axioms Guo62.pochZ_ne_zero
#check Guo62.terminating_denominators
#print axioms Guo62.terminating_denominators
#check Guo62.terminatingTerm_dixon
#print axioms Guo62.terminatingTerm_dixon
#check Guo62.terminatingTerm_zero
#print axioms Guo62.terminatingTerm_zero
#check Guo62.terminatingTerm_at_zero
#print axioms Guo62.terminatingTerm_at_zero
#check Guo62.HasJet.fraction
#print axioms Guo62.HasJet.fraction
#check Guo62.HasJet.const
#print axioms Guo62.HasJet.const
#check Guo62.HasJet.add
#print axioms Guo62.HasJet.add
#check Guo62.HasJet.mul
#print axioms Guo62.HasJet.mul
#check Guo62.HasJet.sum
#print axioms Guo62.HasJet.sum
#check Guo62.HasJet.congSq
#print axioms Guo62.HasJet.congSq
#check Guo62.HasJet.neg
#print axioms Guo62.HasJet.neg
#check Guo62.HasJet.sub
#print axioms Guo62.HasJet.sub
#check Guo62.HasJet.inv
#print axioms Guo62.HasJet.inv
#check Guo62.HasJet.div
#print axioms Guo62.HasJet.div
#check Guo62.HasJet.poly
#print axioms Guo62.HasJet.poly
#check Guo62.HasJet.qpow
#print axioms Guo62.HasJet.qpow
#check Guo62.HasJet.prod
#print axioms Guo62.HasJet.prod
#check Guo62.rhs_poch_split
#print axioms Guo62.rhs_poch_split
#check Guo62.rhs_fraction
#print axioms Guo62.rhs_fraction
#check Guo62.rhsRest_aeval_ne_zero
#print axioms Guo62.rhsRest_aeval_ne_zero
#check Guo62.source_rhs_regular
#print axioms Guo62.source_rhs_regular
#check Guo62.SameJet.refl
#print axioms Guo62.SameJet.refl
#check Guo62.SameJet.mul
#print axioms Guo62.SameJet.mul
#check Guo62.SameJet.div
#print axioms Guo62.SameJet.div
#check Guo62.SameJet.prod
#print axioms Guo62.SameJet.prod
#check Guo62.SameJet.congSq
#print axioms Guo62.SameJet.congSq
#check Guo62.HasJet.qzpow
#print axioms Guo62.HasJet.qzpow
example : Guo62.GuoConjecture62 := Guo62.guo_conj_6_2
```

