# Lean source appendix — MathDB 366674 (Guo–Wang Conjecture 4.1)

66 modules in import order. Each block is byte-identical to `src/<Module>.lean`.
Main endpoint: `GuoWang.guo_wang_conj_4_1` in `GWConjecture.lean`; the review's literal
endpoint is restated and proved in `GWReviewEndpoint.lean`.

### `QWZCore.lean`

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Kernel-checkable algebra used by the written proof of MathDB 366674.
This module does NOT claim the full conjecture. -/
open scoped BigOperators

namespace QWZCore

/-- The cleared A-certificate. The finite-product/rational-summand bridge is separate. -/
theorem certificate_A {K : Type*} [Field K] (a q x : K) (ha : a ≠ 0) :
    let C := (1 - a*q^4)*(1-a^2*q^4);
    let U := (1-a*q*x)*(1-a*q^3*x)*(1-x^2/a) -
      (a*q^3-x)*(a*q-x)*(1-a*q^4*x^2);
    -(x^3/a)*(1-a*q*x)*(1-q*x)*(a*q^3-x)*(-C) -
      (1-x^2)*(1-x^2/a)*(1-a*q^4*x^2)*(-C) =
      (1-a*q^4)*U*(1-q*x^3) := by
  dsimp
  field_simp [ha]
  ring

/-- The cleared B-certificate. -/
theorem certificate_B {K : Type*} [Field K] (a q y : K) (ha : a ≠ 0) :
    let C := (1-a*q^4)*(1-a^2*q^4);
    let U := -(1-a*q^3)*(1-a*q*y)*(1-y/a) -
      (1-a*q)*(a*q^3-y)*(1-a*q^4*y);
    -(y/a)*(1-a*q*y)*(1-q*y)*(a*q^3-y)*C -
      (1-y)*(1-y/a)*(1-a*q^4*y)*C =
      (1-a*q^4)*U*(1-q*y^2) := by
  dsimp
  field_simp [ha]
  ring

/-- Multiplying a cyclic first-order recurrence gives its monodromy obstruction.
This is the finite algebraic part of the cyclic parameter-shift lemma. -/
theorem multiply_recurrence {K : Type*} [CommRing K]
    (p r f : ℕ → K) (n : ℕ)
    (h : ∀ i < n, p i * f (i+1) = r i * f i) :
    (∏ i ∈ Finset.range n, p i) * f n =
      (∏ i ∈ Finset.range n, r i) * f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hi := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc
      ((∏ i ∈ Finset.range n, p i) * p n) * f (n+1) =
          (∏ i ∈ Finset.range n, p i) * (p n * f (n+1)) := by ring
      _ = (∏ i ∈ Finset.range n, p i) * (r n * f n) := by rw [hn]
      _ = r n * ((∏ i ∈ Finset.range n, p i) * f n) := by ring
      _ = r n * ((∏ i ∈ Finset.range n, r i) * f 0) := by rw [hi]
      _ = ((∏ i ∈ Finset.range n, r i) * r n) * f 0 := by ring

/-- A nontrivial cyclic multiplier forces the initial value to vanish. -/
theorem cyclic_zero {K : Type*} [Field K]
    (p r f : ℕ → K) (n : ℕ)
    (h : ∀ i < n, p i * f (i+1) = r i * f i)
    (hcyc : f n = f 0)
    (hne : (∏ i ∈ Finset.range n, p i) ≠ (∏ i ∈ Finset.range n, r i)) :
    f 0 = 0 := by
  have hm := multiply_recurrence p r f n h
  rw [hcyc] at hm
  have hz : ((∏ i ∈ Finset.range n, p i) -
      (∏ i ∈ Finset.range n, r i)) * f 0 = 0 := by
    rw [sub_mul, hm, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

#print axioms certificate_A
#print axioms certificate_B
#print axioms cyclic_zero
end QWZCore
```

### `QProducts.lean`

```lean
import QWZCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
namespace QWZCore

variable {K : Type*} [CommRing K]

def poch (z q : K) (n : ℕ) : K := ∏ j ∈ Finset.range n, (1-z*q^j)

@[simp] theorem poch_zero (z q : K) : poch z q 0 = 1 := by simp [poch]

@[simp] theorem poch_succ (z q : K) (n : ℕ) :
    poch z q (n+1) = poch z q n * (1-z*q^n) := by
  simp only [poch, Finset.prod_range_succ]

/-- Removing one initial factor is a polynomial identity; no division convention is needed. -/
theorem poch_shift (z q : K) (n : ℕ) :
    (1-z) * poch (z*q) q n = poch z q n * (1-z*q^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [poch_succ, poch_succ]
    have hpow : 1-z*q*q^n = 1-z*q^(n+1) := by rw [pow_succ]; ring
    rw [hpow]
    calc
      (1-z)*(poch (z*q) q n*(1-z*q^(n+1))) =
          ((1-z)*poch (z*q) q n)*(1-z*q^(n+1)) := by ring
      _ = (poch z q n*(1-z*q^n))*(1-z*q^(n+1)) := by rw [ih]

/-- Two shifts, used by the bibasic A-summand. -/
theorem poch_shift_two (z q : K) (n : ℕ) :
    (1-z)*(1-z*q)*poch (z*q^2) q n =
      poch z q n*(1-z*q^n)*(1-z*q^(n+1)) := by
  have h₁ := poch_shift z q n
  have h₂ := poch_shift (z*q) q n
  have hbase : z*q*q = z*q^2 := by ring
  have hpow : 1-z*q*q^n = 1-z*q^(n+1) := by rw [pow_succ]; ring
  rw [hbase, hpow] at h₂
  calc
    (1-z)*(1-z*q)*poch (z*q^2) q n =
        (1-z)*((1-z*q)*poch (z*q^2) q n) := by ring
    _ = (1-z)*(poch (z*q) q n*(1-z*q^(n+1))) := by rw [h₂]
    _ = ((1-z)*poch (z*q) q n)*(1-z*q^(n+1)) := by ring
    _ = (poch z q n*(1-z*q^n))*(1-z*q^(n+1)) := by rw [h₁]

/-- A product vanishes once a zero factor has entered its range. -/
theorem poch_eq_zero_of_factor (z q : K) (n j : ℕ) (hj : j < n)
    (hzero : z*q^j = 1) : poch z q n = 0 := by
  unfold poch
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
  rw [hzero, sub_self]

/-- The n-th term, multiplied by its last denominator factor, is polynomially regular. -/
theorem poch_last_factor (z q : K) (n : ℕ) :
    poch z q (n+1) = (1-z*q^n) * poch z q n := by
  rw [poch_succ, mul_comm]

#print axioms poch_shift_two
#print axioms poch_eq_zero_of_factor
end QWZCore
```

### `QCyclic.lean`

```lean
import QWZCore
import Mathlib.FieldTheory.KummerExtension

/-! Root-of-unity finite algebra for the parameter-shift argument.  This is a
helper theorem, not the Guo--Wang conjecture or its vanishing-order bridge. -/
open scoped BigOperators
namespace QWZCore

theorem prod_one_sub_mul_pow {K : Type*} [Field K]
    {z : K} {n : ℕ} (hz : IsPrimitiveRoot z n) (hn : 0 < n) (a : K) :
    (∏ i ∈ Finset.range n, (1-a*z^i)) = 1-a^n := by
  have h := X_pow_sub_C_eq_prod hz hn (α := a) (a := a^n) rfl
  have he := congrArg (Polynomial.eval (1 : K)) h
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod, mul_comm] using he.symm

/-- A finite orbit of a multiplicative parameter has incompatible monodromy
unless its initial value is zero.  The nontriviality condition is automatic for
the transcendental parameter in the written proof. -/
theorem parameter_orbit_zero {K : Type*} [Field K]
    {z : K} {n : ℕ} (hz : IsPrimitiveRoot z n) (hn : 0 < n)
    (a : K) (F : K → K)
    (hrec : ∀ i < n,
      (1-(a*z^i)⁻¹)*F (a*z^(i+1)) = (1-a*z^(i+1))*F (a*z^i))
    (hne : a^n ≠ (a⁻¹)^n) : F a = 0 := by
  let p : ℕ → K := fun i => 1-(a*z^i)⁻¹
  let r : ℕ → K := fun i => 1-a*z^(i+1)
  let f : ℕ → K := fun i => F (a*z^i)
  have hp : (∏ i ∈ Finset.range n, p i) = 1-(a⁻¹)^n := by
    convert prod_one_sub_mul_pow hz.inv hn (a⁻¹) using 1
    simp [p, mul_inv_rev, inv_pow, mul_comm]
  have hr : (∏ i ∈ Finset.range n, r i) = 1-a^n := by
    calc
      (∏ i ∈ Finset.range n, r i) =
          ∏ i ∈ Finset.range n, (1-(a*z)*z^i) := by
        apply Finset.prod_congr rfl
        intro i hi
        dsimp [r]
        rw [pow_succ]
        ring
      _ = 1-(a*z)^n := prod_one_sub_mul_pow hz hn (a*z)
      _ = 1-a^n := by rw [mul_pow, hz.pow_eq_one, mul_one]
  have hc : f n = f 0 := by simp [f, hz.pow_eq_one]
  have hprod : (∏ i ∈ Finset.range n, p i) ≠
      (∏ i ∈ Finset.range n, r i) := by
    rw [hp, hr]
    intro he
    apply hne
    exact (sub_right_injective he).symm
  have hz0 := cyclic_zero p r f n hrec hc hprod
  simpa [f] using hz0

#print axioms prod_one_sub_mul_pow
#print axioms parameter_orbit_zero
end QWZCore
```

### `QSpecialize.lean`

```lean
import QWZCore
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Monic factor extraction in a domain, including the non-comaximal case.
This is useful over Laurent polynomials in q: q^n and q^(-n) are distinct,
but their difference is not a unit at the cyclotomic factor. -/
namespace QWZCore
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

theorem two_distinct_roots_factor (p : R[X]) (r s : R)
    (hr : p.eval r = 0) (hs : p.eval s = 0) (hrs : r ≠ s) :
    ∃ t : R[X], p = (X-C r)*(X-C s)*t := by
  obtain ⟨u, hu⟩ := (dvd_iff_isRoot.mpr hr : X-C r ∣ p)
  have hus : u.eval s = 0 := by
    rw [hu] at hs
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hs
    exact (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hrs.symm)
  obtain ⟨t, ht⟩ := (dvd_iff_isRoot.mpr hus : X-C s ∣ u)
  exact ⟨t, by rw [hu, ht, mul_assoc]⟩

/-- First remove a scalar factor coefficientwise, then the two monic parameter
roots. No Bezout identity or comaximality of the two root ideals is assumed. -/
theorem specialize_scalar_two_roots (p : R[X]) (c r s b : R)
    (hc : c ≠ 0) (hfactor : C c ∣ p)
    (hr : p.eval r = 0) (hs : p.eval s = 0) (hrs : r ≠ s) :
    c*(b-r)*(b-s) ∣ p.eval b := by
  obtain ⟨u, hu⟩ := hfactor
  have hur : u.eval r = 0 := by
    rw [hu] at hr
    simp only [eval_mul, eval_C] at hr
    exact (mul_eq_zero.mp hr).resolve_left hc
  have hus : u.eval s = 0 := by
    rw [hu] at hs
    simp only [eval_mul, eval_C] at hs
    exact (mul_eq_zero.mp hs).resolve_left hc
  obtain ⟨t, ht⟩ := two_distinct_roots_factor u r s hur hus hrs
  refine ⟨t.eval b, ?_⟩
  rw [hu, ht]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  ring

#print axioms two_distinct_roots_factor
#print axioms specialize_scalar_two_roots
end QWZCore
```

### `GWStatement.lean`

```lean
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-! Literal statement of Guo--Wang Conjecture 4.1. The conjecture is a
proposition, not an asserted theorem, until its proof is assembled. -/
open scoped BigOperators
namespace GuoWang
open Polynomial

noncomputable section

def poch (z b : RatFunc ℚ) (k : ℕ) : RatFunc ℚ :=
  ∏ j ∈ Finset.range k, (1 - z * b ^ j)

def qIntPoly (m : ℕ) : ℚ[X] := ∑ j ∈ Finset.range m, X ^ j

def qInt (m : ℕ) : RatFunc ℚ := algebraMap _ _ (qIntPoly m)

def X' : RatFunc ℚ := RatFunc.X

def L (k : ℕ) : RatFunc ℚ :=
  (-1) ^ k * qInt (6*k+1) * poch X' (X'^2) k ^ 3 /
    poch (X'^4) (X'^4) k ^ 3 * X' ^ (3*k^2)

def R (k : ℕ) : RatFunc ℚ :=
  (-1) ^ k * qInt (8*k+1) * poch X' (X'^4) k ^ 3 /
    poch (X'^4) (X'^4) k ^ 3 * X' ^ (2*k^2+k)

def diff (n : ℕ) : RatFunc ℚ :=
  (∑ k ∈ Finset.range n, L k) - (∑ k ∈ Finset.range n, R k)

/-- The exact reviewed endpoint, with no extra denominator assumptions. -/
def Conjecture41 : Prop := ∀ (n : ℕ), 0 < n → n % 4 = 1 →
  qIntPoly n * cyclotomic n ℚ ^ 3 ∣ (diff n).num

@[simp] theorem poch_zero (z b : RatFunc ℚ) : poch z b 0 = 1 := by
  simp [poch]

@[simp] theorem poch_succ (z b : RatFunc ℚ) (k : ℕ) :
    poch z b (k+1) = poch z b k * (1-z*b^k) := by
  simp only [poch, Finset.prod_range_succ]

@[simp] theorem X'_ne_zero : X' ≠ 0 := RatFunc.X_ne_zero

theorem X'_pow_ne_one (m : ℕ) (hm : 0 < m) : X' ^ m ≠ 1 := by
  intro h
  have he : (X : ℚ[X]) ^ m = 1 := RatFunc.algebraMap_injective ℚ (by
    simpa only [map_pow, RatFunc.algebraMap_X, X', map_one] using h)
  have hc := congrArg (fun p : ℚ[X] => p.coeff m) he
  rw [coeff_X_pow_self, coeff_one, ite_eq_right hm.ne'] at hc
  exact one_ne_zero hc

theorem one_sub_X'_pow_ne_zero (m : ℕ) (hm : 0 < m) : 1-X'^m ≠ 0 :=
  sub_ne_zero.mpr (X'_pow_ne_one m hm).symm

/-- The exact denominator required by the independent statement review. -/
theorem poch_den_ne_zero (k : ℕ) : poch (X'^4) (X'^4) k ≠ 0 := by
  unfold poch
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  have he : X'^4 * (X'^4)^j = X'^(4*(j+1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  exact one_sub_X'_pow_ne_zero _ (by omega)

/-- All division in each of the two literal summands is by this nonzero cube. -/
theorem term_den_ne_zero (k : ℕ) : poch (X'^4) (X'^4) k ^ 3 ≠ 0 :=
  pow_ne_zero _ (poch_den_ne_zero k)

theorem qInt_eq_sum (m : ℕ) : qInt m = ∑ j ∈ Finset.range m, X'^j := by
  simp [qInt, qIntPoly, map_sum, X', RatFunc.algebraMap_X]

/-- The source's quotient formula for [m], with no division in its definition. -/
theorem qInt_mul (m : ℕ) : qInt m * (1-X') = 1-X'^m := by
  rw [qInt_eq_sum]
  have h := geom_sum_mul X' m
  linear_combination -h

theorem qInt_source (m : ℕ) : qInt m = (1-X'^m)/(1-X') := by
  have h : 1-X' ≠ 0 := by simpa using one_sub_X'_pow_ne_zero 1 (by omega)
  apply (eq_div_iff h).mpr
  exact qInt_mul m

@[simp] theorem qInt_one : qInt 1 = 1 := by simp [qInt, qIntPoly]

@[simp] theorem L_zero : L 0 = 1 := by simp [L]
@[simp] theorem R_zero : R 0 = 1 := by simp [R]
@[simp] theorem diff_one : diff 1 = 0 := by simp [diff]

/-- The admissible n=1 case is an actual equality of the two singleton sums. -/
theorem guo_wang_conj_4_1_one : qIntPoly 1 * cyclotomic 1 ℚ ^ 3 ∣ (diff 1).num := by
  simp

#print Conjecture41
#print axioms poch_den_ne_zero
#print axioms term_den_ne_zero
#print axioms qInt_source
#print axioms guo_wang_conj_4_1_one
end
end GuoWang
```

### `GWRatBridge.lean`

```lean
import GWStatement
import Mathlib.RingTheory.Coprime.Basic

/-! Bridges involving the *reduced* rational-function numerator.
The coprimality guard is essential: common denominators at proper divisors
of n need not be units modulo [n]. -/
namespace GuoWang
open Polynomial
noncomputable section

/-- Clearing any nonzero denominator yields an honest polynomial equality. -/
theorem reduced_cross_mul (f : RatFunc ℚ) (p d : ℚ[X]) (hd : d ≠ 0)
    (hf : f = algebraMap _ _ p / algebraMap _ _ d) :
    f.num * d = p * f.denom :=
  (RatFunc.num_mul_eq_mul_denom_iff hd).mpr hf

/-- Divisibility of the reduced numerator implies divisibility of every
numerator obtained with a nonzero polynomial denominator. -/
theorem reduced_num_dvd_cleared (f : RatFunc ℚ) (p d : ℚ[X]) (hd : d ≠ 0)
    (hf : f = algebraMap _ _ p / algebraMap _ _ d) : f.num ∣ p := by
  rw [hf]
  exact RatFunc.num_div_dvd p hd

/-- When the chosen denominator is coprime to the modulus, clearing it
preserves precisely the source's reduced-numerator congruence. -/
theorem modulus_dvd_reduced_num_iff (f : RatFunc ℚ) (p d M : ℚ[X])
    (hd : d ≠ 0) (hf : f = algebraMap _ _ p / algebraMap _ _ d)
    (hMd : IsCoprime M d) : M ∣ f.num ↔ M ∣ p := by
  constructor
  · intro h
    exact h.trans (reduced_num_dvd_cleared f p d hd hf)
  · intro h
    apply hMd.dvd_of_dvd_mul_right
    rw [reduced_cross_mul f p d hd hf]
    exact dvd_mul_of_dvd_left h _

/-- A zero at a legal specialization can be read after clearing its denominator.
No claim is made about a specialization whose denominator vanishes. -/
theorem quotient_zero_iff (p d : ℚ[X]) (hd : d ≠ 0) :
    (algebraMap ℚ[X] (RatFunc ℚ) p / algebraMap _ _ d = 0) ↔ p = 0 := by
  rw [div_eq_zero_iff, or_iff_left (RatFunc.algebraMap_ne_zero hd)]
  exact (RatFunc.algebraMap_injective ℚ).eq_iff' (map_zero _)

/-- In particular every endpoint reduced denominator is nonzero, independently
of any later use of a larger common denominator. -/
theorem diff_reduced_den_ne_zero (n : ℕ) : (diff n).denom ≠ 0 :=
  RatFunc.denom_ne_zero _

#print axioms reduced_cross_mul
#print axioms reduced_num_dvd_cleared
#print axioms modulus_dvd_reduced_num_iff
#print axioms quotient_zero_iff
#print axioms diff_reduced_den_ne_zero
end
end GuoWang
```

### `GWParametric.lean`

```lean
import GWStatement
import QProducts

/-! Explicit auxiliary families; their a=1 bridge is proved in Lean. -/
open scoped BigOperators
namespace GuoWang
noncomputable section

def paramDen (q a : RatFunc ℚ) (k : ℕ) : RatFunc ℚ :=
  poch (a*q^4) (q^4) k * poch (q^4/a) (q^4) k * poch (q^4) (q^4) k

def A (q a : RatFunc ℚ) (k : ℕ) : RatFunc ℚ :=
  (-1)^k * (∑ j ∈ Finset.range (6*k+1), q^j) * q^(3*k^2) *
    (poch (a*q) (q^2) k * poch (q/a) (q^2) k * poch q (q^2) k) / paramDen q a k

def B (q a : RatFunc ℚ) (k : ℕ) : RatFunc ℚ :=
  (-1)^k * (∑ j ∈ Finset.range (8*k+1), q^j) * q^(2*k^2+k) *
    (poch (a*q) (q^4) k * poch (q/a) (q^4) k * poch q (q^4) k) / paramDen q a k

def D (N : ℕ) (q a : RatFunc ℚ) : RatFunc ℚ :=
  (∑ k ∈ Finset.range N, A q a k) - (∑ k ∈ Finset.range N, B q a k)

theorem poch_eq_core (z b : RatFunc ℚ) (k : ℕ) :
    poch z b k = QWZCore.poch z b k := rfl

theorem paramDen_one (k : ℕ) : paramDen X' 1 k = poch (X'^4) (X'^4) k ^ 3 := by
  simp only [paramDen, one_mul, div_one]
  ring

theorem paramDen_one_ne_zero (k : ℕ) : paramDen X' 1 k ≠ 0 := by
  rw [paramDen_one]
  exact term_den_ne_zero k

theorem A_one (k : ℕ) : A X' 1 k = L k := by
  simp only [A, L, one_mul, div_one, paramDen_one, qInt_eq_sum]
  ring

theorem B_one (k : ℕ) : B X' 1 k = R k := by
  simp only [B, R, one_mul, div_one, paramDen_one, qInt_eq_sum]
  ring

theorem D_one (N : ℕ) : D N X' 1 = diff N := by
  simp only [D, diff, A_one, B_one]

/-- General positive-exponent denominator factor, proved before specialization. -/
theorem poch_pos_ne_zero (t s k : ℕ) (ht : 0 < t) : poch (X'^t) (X'^s) k ≠ 0 := by
  unfold poch
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  have he : X'^t * (X'^s)^j = X'^(t+s*j) := by rw [← pow_mul, pow_add]
  rw [he]
  exact one_sub_X'_pow_ne_zero _ (by omega)

/-- At a=q the denominator does not disappear, even though the numerator terminates. -/
theorem paramDen_q_ne_zero (k : ℕ) : paramDen X' X' k ≠ 0 := by
  have hmul : X'*X'^4 = X'^5 := by ring
  have hdiv : X'^4/X' = X'^3 := by
    apply (div_eq_iff X'_ne_zero).mpr
    ring
  simp only [paramDen, hmul, hdiv]
  exact mul_ne_zero (mul_ne_zero (poch_pos_ne_zero 5 4 k (by omega))
    (poch_pos_ne_zero 3 4 k (by omega))) (poch_pos_ne_zero 4 4 k (by omega))

theorem poch_one_eq_zero (b : RatFunc ℚ) (k : ℕ) (hk : 0 < k) : poch 1 b k = 0 := by
  rw [poch_eq_core]
  exact QWZCore.poch_eq_zero_of_factor 1 b k 0 hk (by simp)

theorem A_at_q_zero (k : ℕ) (hk : 0 < k) : A X' X' k = 0 := by
  simp [A, poch_one_eq_zero _ _ hk]

theorem B_at_q_zero (k : ℕ) (hk : 0 < k) : B X' X' k = 0 := by
  simp [B, poch_one_eq_zero _ _ hk]

@[simp] theorem A_zero (q a : RatFunc ℚ) : A q a 0 = 1 := by simp [A, paramDen]
@[simp] theorem B_zero (q a : RatFunc ℚ) : B q a 0 = 1 := by simp [B, paramDen]

/-- The initial terminating parameter equality, without a summation formula. -/
theorem D_at_q (N : ℕ) : D N X' X' = 0 := by
  unfold D
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = 0
  · simp [hk]
  · rw [A_at_q_zero k (Nat.pos_of_ne_zero hk), B_at_q_zero k (Nat.pos_of_ne_zero hk)]

#print axioms paramDen_one_ne_zero
#print axioms A_one
#print axioms B_one
#print axioms D_one
#print axioms paramDen_q_ne_zero
#print axioms D_at_q
end
end GuoWang
```

### `GWCyclotomic.lean`

```lean
import GWRatBridge
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Coprime.Lemmas

/-! Units of unparametrized short-sum denominators at the top cyclotomic
factor. The same assertion is deliberately not made at proper divisors. -/
open scoped BigOperators
namespace GuoWang
open Polynomial
noncomputable section

def denPoly (k : ℕ) : ℚ[X] := ∏ j ∈ Finset.range k, (1-X^(4*(j+1)))

theorem map_denPoly (k : ℕ) : algebraMap ℚ[X] (RatFunc ℚ) (denPoly k) =
    poch (X'^4) (X'^4) k := by
  simp only [denPoly, poch, map_prod, map_sub, map_one, map_pow, RatFunc.algebraMap_X]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  dsimp [X']
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

theorem denPoly_ne_zero (k : ℕ) : denPoly k ≠ 0 := by
  intro h
  apply poch_den_ne_zero k
  rw [← map_denPoly, h, map_zero]

theorem coprime_cyclotomic_one_sub_pow (n m : ℕ) (hm : 0 < m) (hnm : ¬ n ∣ m) :
    IsCoprime (cyclotomic n ℚ) (1-(X : ℚ[X])^m) := by
  have h : IsCoprime (cyclotomic n ℚ) ((X : ℚ[X])^m-1) := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one hm ℚ]
    apply IsCoprime.prod_right_iff.mpr
    intro d hd
    apply cyclotomic.isCoprime_rat
    intro he
    apply hnm
    subst d
    exact (Nat.mem_divisors.mp hd).1
  simpa only [neg_sub] using h.neg_right

/-- Each endpoint term k<n has denominator a unit modulo Φ_n, including
composite n; this uses n≡1 mod 4, not primality. -/
theorem coprime_denPoly_top (n k : ℕ) (h4 : n % 4 = 1) (hk : k < n) :
    IsCoprime (cyclotomic n ℚ) (denPoly k) := by
  have hc : n.Coprime 4 := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm n 4, Nat.gcd_rec, h4]
    decide
  unfold denPoly
  apply IsCoprime.prod_right_iff.mpr
  intro j hj
  apply coprime_cyclotomic_one_sub_pow n (4*(j+1)) (by omega)
  intro hdiv
  have hjn : j+1 < n := by have := Finset.mem_range.mp hj; omega
  have hnj := hc.dvd_mul_left.mp hdiv
  exact (Nat.not_dvd_of_pos_of_lt (by omega) hjn) hnj

theorem coprime_denPoly_cube_top (n k : ℕ) (h4 : n % 4 = 1) (hk : k < n) :
    IsCoprime (cyclotomic n ℚ ^ 4) (denPoly k ^ 3) :=
  (coprime_denPoly_top n k h4 hk).pow

#print axioms map_denPoly
#print axioms denPoly_ne_zero
#print axioms coprime_cyclotomic_one_sub_pow
#print axioms coprime_denPoly_top
#print axioms coprime_denPoly_cube_top
end
end GuoWang
```

### `GWTerminatingDen.lean`

```lean
import GWParametric

/-! Nonvanishing at all positive terminating parameters used in the proof,
and exact zero-factor locations. These facts do not assert the WZ recurrence. -/
namespace GuoWang
noncomputable section
open Polynomial

theorem X'_pow_injective : Function.Injective (fun k : ℕ => X'^k) := by
  intro i j hij
  have he : (X : ℚ[X]) ^ i = X ^ j := RatFunc.algebraMap_injective ℚ (by
    simpa only [map_pow, RatFunc.algebraMap_X, X'] using hij)
  have hc := congrArg (fun p : ℚ[X] => p.coeff i) he
  by_contra hne
  rw [coeff_X_pow_self, coeff_X_pow, ite_eq_right hne] at hc
  exact one_ne_zero hc

/-- No denominator Pochhammer vanishes at a=q^e when e≡1 mod 4.
This applies to q, every intermediate q^(4j+1), and q^n. -/
theorem paramDen_qpow_ne_zero (e k : ℕ) (he : e % 4 = 1) :
    paramDen X' (X'^e) k ≠ 0 := by
  have ht : 0 < e+4 := by omega
  have hp : X'^e*X'^4 = X'^(e+4) := by rw [pow_add]
  have hright : poch (X'^4/X'^e) (X'^4) k ≠ 0 := by
    unfold poch
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have hf : X'^4/X'^e*(X'^4)^j = X'^(4*(j+1))/X'^e := by
      rw [div_mul_eq_mul_div, ← pow_mul, ← pow_add]
      congr 2
      omega
    rw [hf]
    apply sub_ne_zero.mpr
    intro hz
    have hz' : X'^(4*(j+1)) = X'^e := by
      have := (div_eq_one_iff_eq (pow_ne_zero e X'_ne_zero)).mp hz.symm
      exact this
    have hexp := X'_pow_injective hz'
    omega
  simp only [paramDen, hp]
  exact mul_ne_zero (mul_ne_zero (poch_pos_ne_zero (e+4) 4 k ht) hright)
    (poch_den_ne_zero k)

theorem paramDen_inv (q a : RatFunc ℚ) (k : ℕ) :
    paramDen q a⁻¹ k = paramDen q a k := by
  simp only [paramDen, div_eq_mul_inv, inv_inv, mul_comm]

theorem paramDen_qpow_inv_ne_zero (e k : ℕ) (he : e % 4 = 1) :
    paramDen X' (X'^e)⁻¹ k ≠ 0 := by
  rw [paramDen_inv]
  exact paramDen_qpow_ne_zero e k he

/-- The zero factor is at exactly j=(e-1)/s, when it lies in the range. -/
theorem terminating_poch_zero (s j k : ℕ) (hj : j < k) :
    poch (X'/X'^(s*j+1)) (X'^s) k = 0 := by
  rw [poch_eq_core]
  apply QWZCore.poch_eq_zero_of_factor _ _ k j hj
  rw [div_mul_eq_mul_div, ← pow_mul]
  have hp : X' * X'^(s*j) = X'^(s*j+1) := by rw [pow_succ']
  rw [hp, div_self (pow_ne_zero _ X'_ne_zero)]

theorem terminating_A_poch_zero (j N : ℕ) (hj : 2*j < N) :
    poch (X'/X'^(4*j+1)) (X'^2) N = 0 := by
  simpa only [show 2*(2*j)+1 = 4*j+1 by omega] using terminating_poch_zero 2 (2*j) N hj

theorem terminating_B_poch_zero (j N : ℕ) (hj : j < N) :
    poch (X'/X'^(4*j+1)) (X'^4) N = 0 :=
  terminating_poch_zero 4 j N hj

#print axioms X'_pow_injective
#print axioms paramDen_qpow_ne_zero
#print axioms paramDen_qpow_inv_ne_zero
#print axioms terminating_A_poch_zero
#print axioms terminating_B_poch_zero
end
end GuoWang
```

### `GWProductRatios.lean`

```lean
import QProducts

/-! Legal rational versions of the division-free finite product shifts.
Unlike cancelling an entire summand, these lemmas do not require the product
being shifted to be nonzero. This matters at terminating parameters. -/
namespace GuoWang.WZ
open QWZCore
variable {K : Type*} [Field K]

theorem poch_forward_ratio (z b : K) (k : ℕ) (hz : 1-z ≠ 0) :
    poch (z*b) b k = poch z b k*(1-z*b^k)/(1-z) := by
  apply (eq_div_iff hz).mpr
  rw [mul_comm (poch (z*b) b k)]
  exact poch_shift z b k

theorem poch_forward_two_ratio (z b : K) (k : ℕ)
    (hz : 1-z ≠ 0) (hzb : 1-z*b ≠ 0) :
    poch (z*b^2) b k =
      poch z b k*(1-z*b^k)*(1-z*b^(k+1))/((1-z)*(1-z*b)) := by
  apply (eq_div_iff (mul_ne_zero hz hzb)).mpr
  rw [mul_comm (poch (z*b^2) b k)]
  exact poch_shift_two z b k

theorem poch_backward_ratio (z b : K) (k : ℕ) (hb : b ≠ 0)
    (hz : 1-z/b*b^k ≠ 0) :
    poch (z/b) b k = poch z b k*(1-z/b)/(1-z/b*b^k) := by
  have h := poch_shift (z/b) b k
  rw [div_mul_cancel₀ z hb] at h
  apply (eq_div_iff hz).mpr
  rw [← h, mul_comm]

/-- A ratio-free increment identity remains legal at zero numerator factors. -/
theorem triple_poch_succ (u v w b : K) (k : ℕ) :
    poch u b (k+1)*poch v b (k+1)*poch w b (k+1) =
      (poch u b k*poch v b k*poch w b k)*
        ((1-u*b^k)*(1-v*b^k)*(1-w*b^k)) := by
  rw [poch_succ, poch_succ, poch_succ]
  ring

#print axioms poch_forward_ratio
#print axioms poch_forward_two_ratio
#print axioms poch_backward_ratio
#print axioms triple_poch_succ
end GuoWang.WZ
```

### `GWRationalB.lean`

```lean
import QWZCore

/-! The B certificate as an actual rational identity, including its shifted
boundary ratio. Connecting the ratios to finite Pochhammer summands is a
separate obligation; this module makes no claim to have discharged it. -/
namespace GuoWang.WZ
variable {K : Type*} [Field K]

def c (q a : K) : K := (1-a*q^4)*(1-a^2*q^4)

def gB (q a y : K) : K :=
  c q a*(1-y)*(1-y/a)/((1-q*y^2)*(a*q^3-y)*(1-a*q))

def shiftB (q a y : K) : K :=
  (1-a*q^4)*(-(1-a*q^3)*(1-a*q*y)*(1-y/a))/
    ((1-a⁻¹)*(1-a*q)*(a*q^3-y)*(1-a*q^4*y))

def nextB (q a y : K) : K :=
  -q^3*y*(1-q^9*y^2)/(1-q*y^2)*
    ((1-a*q*y)*(1-q*y/a)*(1-q*y))/
    ((1-a*q^4*y)*(1-q^4*y/a)*(1-q^4*y))

/-- A legal cancellation of the next-term ratio with the next certificate. -/
theorem nextB_gB (q a y : K) (ha : a ≠ 0)
    (_h₁ : 1-q*y^2 ≠ 0) (_h₂ : 1-a*q ≠ 0)
    (_h₃ : 1-a*q^4*y ≠ 0) (_h₄ : 1-q^4*y/a ≠ 0)
    (_h₅ : 1-q^4*y ≠ 0) (_h₆ : 1-q^9*y^2 ≠ 0)
    (_h₇ : a*q^3-q^4*y ≠ 0) :
    nextB q a y * gB q a (q^4*y) =
      -(y/a)*(1-a*q*y)*(1-q*y)*c q a /
        ((1-q*y^2)*(1-a*q^4*y)*(1-a*q)) := by
  have hq : q ≠ 0 := by
    intro heq
    simp [heq] at _h₇
  have hlast : a-q*y ≠ 0 := by
    intro heq
    apply _h₇
    calc
      a*q^3-q^4*y = q^3*(a-q*y) := by ring
      _ = 0 := by rw [heq, mul_zero]
  have hsub : a-q^4*y ≠ 0 := by
    intro heq
    apply _h₄
    rw [(sub_eq_zero.mp heq).symm, div_self ha, sub_self]
  have he : 1-q*(q^4*y)^2 = 1-q^9*y^2 := by ring
  dsimp [nextB, gB]
  rw [he]
  field_simp [ha, _h₁, _h₂, _h₃, _h₄, _h₅, _h₆, _h₇, hsub, hq, hlast]

/-- The normalized local B recurrence, with every denominator visibly guarded. -/
theorem rational_certificate_B (q a y : K) (ha : a ≠ 0)
    (_h₀ : 1-a⁻¹ ≠ 0) (_h₁ : 1-q*y^2 ≠ 0)
    (_h₂ : 1-a*q ≠ 0) (_h₃ : 1-a*q^4*y ≠ 0)
    (_h₄ : a*q^3-y ≠ 0) (_h₅ : 1-q^4*y/a ≠ 0)
    (_h₆ : 1-q^4*y ≠ 0) (_h₇ : 1-q^9*y^2 ≠ 0)
    (_h₈ : a*q^3-q^4*y ≠ 0) :
    (1-a⁻¹)*shiftB q a y-(1-a*q^4) =
      nextB q a y*gB q a (q^4*y)-gB q a y := by
  rw [nextB_gB q a y ha _h₁ _h₂ _h₃ _h₅ _h₆ _h₇ _h₈]
  have hsub : a-1 ≠ 0 := by
    intro heq
    have := sub_eq_zero.mp heq
    simp [this] at _h₀
  dsimp [shiftB, gB, c]
  field_simp [ha, _h₀, _h₁, _h₂, _h₃, _h₄, hsub]
  ring

#print axioms nextB_gB
#print axioms rational_certificate_B
end GuoWang.WZ
```

### `GWRationalA.lean`

```lean
import GWRationalB

/-! Rational form of the bibasic A certificate. The finite-product ratio
bridge is deliberately distinguished from this local field identity. -/
namespace GuoWang.WZ
variable {K : Type*} [Field K]

def gA (q a x : K) : K :=
  -c q a*(1-x^2)*(1-x^2/a)/((1-q*x^3)*(a*q^3-x)*(a*q-x))

def shiftA (q a x : K) : K :=
  (1-a*q^4)*(1-a*q*x)*(1-a*q^3*x)*(1-x^2/a)/
    ((1-a⁻¹)*(a*q^3-x)*(a*q-x)*(1-a*q^4*x^2))

def nextA (q a x : K) : K :=
  -q^3*x^3*(1-q^7*x^3)/(1-q*x^3)*
    ((1-a*q*x)*(1-q*x/a)*(1-q*x))/
    ((1-a*q^4*x^2)*(1-q^4*x^2/a)*(1-q^4*x^2))

theorem nextA_gA (q a x : K) (ha : a ≠ 0)
    (_h₁ : 1-q*x^3 ≠ 0) (_h₂ : a*q-x ≠ 0)
    (_h₃ : 1-a*q^4*x^2 ≠ 0) (_h₄ : 1-q^4*x^2/a ≠ 0)
    (_h₅ : 1-q^4*x^2 ≠ 0) (_h₆ : 1-q^7*x^3 ≠ 0)
    (_h₇ : a*q^3-q^2*x ≠ 0) (_h₈ : a*q-q^2*x ≠ 0) :
    nextA q a x*gA q a (q^2*x) =
      (x^3/a)*(1-a*q*x)*(1-q*x)*c q a/
        ((1-q*x^3)*(a*q-x)*(1-a*q^4*x^2)) := by
  have hq : q ≠ 0 := by
    intro heq
    simp [heq] at _h₈
  have hlast : a-q*x ≠ 0 := by
    intro heq
    apply _h₈
    calc
      a*q-q^2*x = q*(a-q*x) := by ring
      _ = 0 := by rw [heq, mul_zero]
  have hsub : a-q^4*x^2 ≠ 0 := by
    intro heq
    apply _h₄
    rw [(sub_eq_zero.mp heq).symm, div_self ha, sub_self]
  have he : 1-q*(q^2*x)^3 = 1-q^7*x^3 := by ring
  have he₂ : (q^2*x)^2 = q^4*x^2 := by ring
  dsimp [nextA, gA]
  rw [he, he₂]
  field_simp [ha, _h₁, _h₂, _h₃, _h₄, _h₅, _h₆, _h₇, _h₈, hsub, hq, hlast]

theorem rational_certificate_A (q a x : K) (ha : a ≠ 0)
    (_h₀ : 1-a⁻¹ ≠ 0) (_h₁ : 1-q*x^3 ≠ 0)
    (_h₂ : a*q-x ≠ 0) (_h₃ : 1-a*q^4*x^2 ≠ 0)
    (_h₄ : a*q^3-x ≠ 0) (_h₅ : 1-q^4*x^2/a ≠ 0)
    (_h₆ : 1-q^4*x^2 ≠ 0) (_h₇ : 1-q^7*x^3 ≠ 0)
    (_h₈ : a*q^3-q^2*x ≠ 0) (_h₉ : a*q-q^2*x ≠ 0) :
    (1-a⁻¹)*shiftA q a x-(1-a*q^4) =
      nextA q a x*gA q a (q^2*x)-gA q a x := by
  rw [nextA_gA q a x ha _h₁ _h₂ _h₃ _h₅ _h₆ _h₇ _h₈ _h₉]
  have hsub : a-1 ≠ 0 := by
    intro heq
    have := sub_eq_zero.mp heq
    simp [this] at _h₀
  dsimp [shiftA, gA, c]
  field_simp [ha, _h₀, _h₁, _h₂, _h₃, _h₄, hsub]
  ring

#print axioms nextA_gA
#print axioms rational_certificate_A
end GuoWang.WZ
```

### `GWTelescope.lean`

```lean
import QWZCore
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Reusable exact finite telescoping, independent of any congruence. -/
open scoped BigOperators
namespace GuoWang.WZ
variable {K : Type*} [CommRing K]

theorem sum_first_difference (g : ℕ → K) (N : ℕ) :
    (∑ k ∈ Finset.range N, (g (k+1)-g k)) = g N-g 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

theorem finite_shift_recurrence (u v g : ℕ → K) (p r : K) (N : ℕ)
    (hstep : ∀ k < N, p*u k-r*v k = g (k+1)-g k) (hzero : g 0 = 0) :
    p*(∑ k ∈ Finset.range N, u k)-r*(∑ k ∈ Finset.range N, v k) = g N := by
  calc
    _ = ∑ k ∈ Finset.range N, (p*u k-r*v k) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ k ∈ Finset.range N, (g (k+1)-g k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hstep k (Finset.mem_range.mp hk)
    _ = g N := by rw [sum_first_difference, hzero, sub_zero]

/-- The common inhomogeneous recurrence for a difference of two finite sums,
once both actual local certificate identities have been proved. -/
theorem finite_difference_recurrence (uA vA uB vB gA gB : ℕ → K)
    (p r : K) (N : ℕ)
    (hA : ∀ k < N, p*uA k-r*vA k = gA (k+1)-gA k)
    (hB : ∀ k < N, p*uB k-r*vB k = gB (k+1)-gB k)
    (hzA : gA 0 = 0) (hzB : gB 0 = 0) :
    p*((∑ k ∈ Finset.range N, uA k)-(∑ k ∈ Finset.range N, uB k)) -
      r*((∑ k ∈ Finset.range N, vA k)-(∑ k ∈ Finset.range N, vB k)) =
        gA N-gB N := by
  have ha := finite_shift_recurrence uA vA gA p r N hA hzA
  have hb := finite_shift_recurrence uB vB gB p r N hB hzB
  calc
    _ = (p*(∑ k ∈ Finset.range N, uA k)-r*(∑ k ∈ Finset.range N, vA k)) -
      (p*(∑ k ∈ Finset.range N, uB k)-r*(∑ k ∈ Finset.range N, vB k)) := by ring
    _ = _ := by rw [ha, hb]

#print axioms sum_first_difference
#print axioms finite_shift_recurrence
#print axioms finite_difference_recurrence
end GuoWang.WZ
```

### `GWAudit.lean`

```lean
import QWZCore
import QProducts
import QCyclic
import QSpecialize
import GWStatement
import GWRatBridge
import GWParametric
import GWCyclotomic
import GWTerminatingDen
import GWProductRatios
import GWRationalB
import GWRationalA
import GWTelescope

/-! All theorem types and axiom reports for this partial certificate. -/
#eval Lean.versionString
#print GuoWang.Conjecture41
#check @QWZCore.certificate_A
#print axioms QWZCore.certificate_A
#check @QWZCore.certificate_B
#print axioms QWZCore.certificate_B
#check @QWZCore.multiply_recurrence
#print axioms QWZCore.multiply_recurrence
#check @QWZCore.cyclic_zero
#print axioms QWZCore.cyclic_zero
#check @QWZCore.poch_zero
#print axioms QWZCore.poch_zero
#check @QWZCore.poch_succ
#print axioms QWZCore.poch_succ
#check @QWZCore.poch_shift
#print axioms QWZCore.poch_shift
#check @QWZCore.poch_shift_two
#print axioms QWZCore.poch_shift_two
#check @QWZCore.poch_eq_zero_of_factor
#print axioms QWZCore.poch_eq_zero_of_factor
#check @QWZCore.poch_last_factor
#print axioms QWZCore.poch_last_factor
#check @QWZCore.prod_one_sub_mul_pow
#print axioms QWZCore.prod_one_sub_mul_pow
#check @QWZCore.parameter_orbit_zero
#print axioms QWZCore.parameter_orbit_zero
#check @QWZCore.two_distinct_roots_factor
#print axioms QWZCore.two_distinct_roots_factor
#check @QWZCore.specialize_scalar_two_roots
#print axioms QWZCore.specialize_scalar_two_roots
#check @GuoWang.poch_zero
#print axioms GuoWang.poch_zero
#check @GuoWang.poch_succ
#print axioms GuoWang.poch_succ
#check @GuoWang.X'_ne_zero
#print axioms GuoWang.X'_ne_zero
#check @GuoWang.X'_pow_ne_one
#print axioms GuoWang.X'_pow_ne_one
#check @GuoWang.one_sub_X'_pow_ne_zero
#print axioms GuoWang.one_sub_X'_pow_ne_zero
#check @GuoWang.poch_den_ne_zero
#print axioms GuoWang.poch_den_ne_zero
#check @GuoWang.term_den_ne_zero
#print axioms GuoWang.term_den_ne_zero
#check @GuoWang.qInt_eq_sum
#print axioms GuoWang.qInt_eq_sum
#check @GuoWang.qInt_mul
#print axioms GuoWang.qInt_mul
#check @GuoWang.qInt_source
#print axioms GuoWang.qInt_source
#check @GuoWang.qInt_one
#print axioms GuoWang.qInt_one
#check @GuoWang.L_zero
#print axioms GuoWang.L_zero
#check @GuoWang.R_zero
#print axioms GuoWang.R_zero
#check @GuoWang.diff_one
#print axioms GuoWang.diff_one
#check @GuoWang.guo_wang_conj_4_1_one
#print axioms GuoWang.guo_wang_conj_4_1_one
#check @GuoWang.reduced_cross_mul
#print axioms GuoWang.reduced_cross_mul
#check @GuoWang.reduced_num_dvd_cleared
#print axioms GuoWang.reduced_num_dvd_cleared
#check @GuoWang.modulus_dvd_reduced_num_iff
#print axioms GuoWang.modulus_dvd_reduced_num_iff
#check @GuoWang.quotient_zero_iff
#print axioms GuoWang.quotient_zero_iff
#check @GuoWang.diff_reduced_den_ne_zero
#print axioms GuoWang.diff_reduced_den_ne_zero
#check @GuoWang.poch_eq_core
#print axioms GuoWang.poch_eq_core
#check @GuoWang.paramDen_one
#print axioms GuoWang.paramDen_one
#check @GuoWang.paramDen_one_ne_zero
#print axioms GuoWang.paramDen_one_ne_zero
#check @GuoWang.A_one
#print axioms GuoWang.A_one
#check @GuoWang.B_one
#print axioms GuoWang.B_one
#check @GuoWang.D_one
#print axioms GuoWang.D_one
#check @GuoWang.poch_pos_ne_zero
#print axioms GuoWang.poch_pos_ne_zero
#check @GuoWang.paramDen_q_ne_zero
#print axioms GuoWang.paramDen_q_ne_zero
#check @GuoWang.poch_one_eq_zero
#print axioms GuoWang.poch_one_eq_zero
#check @GuoWang.A_at_q_zero
#print axioms GuoWang.A_at_q_zero
#check @GuoWang.B_at_q_zero
#print axioms GuoWang.B_at_q_zero
#check @GuoWang.A_zero
#print axioms GuoWang.A_zero
#check @GuoWang.B_zero
#print axioms GuoWang.B_zero
#check @GuoWang.D_at_q
#print axioms GuoWang.D_at_q
#check @GuoWang.map_denPoly
#print axioms GuoWang.map_denPoly
#check @GuoWang.denPoly_ne_zero
#print axioms GuoWang.denPoly_ne_zero
#check @GuoWang.coprime_cyclotomic_one_sub_pow
#print axioms GuoWang.coprime_cyclotomic_one_sub_pow
#check @GuoWang.coprime_denPoly_top
#print axioms GuoWang.coprime_denPoly_top
#check @GuoWang.coprime_denPoly_cube_top
#print axioms GuoWang.coprime_denPoly_cube_top
#check @GuoWang.X'_pow_injective
#print axioms GuoWang.X'_pow_injective
#check @GuoWang.paramDen_qpow_ne_zero
#print axioms GuoWang.paramDen_qpow_ne_zero
#check @GuoWang.paramDen_inv
#print axioms GuoWang.paramDen_inv
#check @GuoWang.paramDen_qpow_inv_ne_zero
#print axioms GuoWang.paramDen_qpow_inv_ne_zero
#check @GuoWang.terminating_poch_zero
#print axioms GuoWang.terminating_poch_zero
#check @GuoWang.terminating_A_poch_zero
#print axioms GuoWang.terminating_A_poch_zero
#check @GuoWang.terminating_B_poch_zero
#print axioms GuoWang.terminating_B_poch_zero
#check @GuoWang.WZ.poch_forward_ratio
#print axioms GuoWang.WZ.poch_forward_ratio
#check @GuoWang.WZ.poch_forward_two_ratio
#print axioms GuoWang.WZ.poch_forward_two_ratio
#check @GuoWang.WZ.poch_backward_ratio
#print axioms GuoWang.WZ.poch_backward_ratio
#check @GuoWang.WZ.triple_poch_succ
#print axioms GuoWang.WZ.triple_poch_succ
#check @GuoWang.WZ.nextB_gB
#print axioms GuoWang.WZ.nextB_gB
#check @GuoWang.WZ.rational_certificate_B
#print axioms GuoWang.WZ.rational_certificate_B
#check @GuoWang.WZ.nextA_gA
#print axioms GuoWang.WZ.nextA_gA
#check @GuoWang.WZ.rational_certificate_A
#print axioms GuoWang.WZ.rational_certificate_A
#check @GuoWang.WZ.sum_first_difference
#print axioms GuoWang.WZ.sum_first_difference
#check @GuoWang.WZ.finite_shift_recurrence
#print axioms GuoWang.WZ.finite_shift_recurrence
#check @GuoWang.WZ.finite_difference_recurrence
#print axioms GuoWang.WZ.finite_difference_recurrence
```

### `GWClearProducts.lean`

```lean
import GWParametric
import Mathlib.Algebra.Polynomial.BigOperators

/-! Polynomial witnesses in the independent parameter. Numerator and denominator
are multiplied by exactly a^k, so no inverse parameter remains in the witnesses.
All maps below are polynomial maps, never totalized RatFunc evaluation. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Three numerator factors at exponent 1+s*j, after clearing a^{-1}. -/
def pairPoch (q : R) (t s k : ℕ) : Polynomial R :=
  ∏ j ∈ Finset.range k,
    ((1-X*C (q^(t+s*j))) * (X-C (q^(t+s*j))) * C (1-q^(t+s*j)))

def den (q : R) (k : ℕ) : Polynomial R := pairPoch q 4 4 k

def num (q : R) (s w e k : ℕ) : Polynomial R :=
  C ((-1:R)^k * (∑ j ∈ Finset.range (w*k+1), q^j) * q^e) * pairPoch q 1 s k

@[simp] theorem map_pairPoch (f : R →+* S) (q : R) (t s k : ℕ) :
    (pairPoch q t s k).map f = pairPoch (f q) t s k := by
  simp [pairPoch, Polynomial.map_prod]

@[simp] theorem map_den (f : R →+* S) (q : R) (k : ℕ) :
    (den q k).map f = den (f q) k := map_pairPoch f q 4 4 k

@[simp] theorem map_num (f : R →+* S) (q : R) (s w e k : ℕ) :
    (num q s w e k).map f = num (f q) s w e k := by
  simp [num, Polynomial.map_sum]

@[simp] theorem eval_pairPoch (q a : R) (t s k : ℕ) :
    (pairPoch q t s k).eval a =
      ∏ j ∈ Finset.range k, ((1-a*q^(t+s*j))*(a-q^(t+s*j))*(1-q^(t+s*j))) := by
  simp [pairPoch, eval_prod]

/-- Exact cancellation accounting; does not divide by a numerator product. -/
theorem eval_pairPoch_field {K : Type*} [Field K] (q a : K) (t s k : ℕ)
    (ha : a ≠ 0) :
    (pairPoch q t s k).eval a = a^k *
      (QWZCore.poch (a*q^t) (q^s) k * QWZCore.poch (q^t/a) (q^s) k *
        QWZCore.poch (q^t) (q^s) k) := by
  rw [eval_pairPoch]
  simp only [QWZCore.poch, ← Finset.prod_mul_distrib]
  have he : a^k = ∏ _j ∈ Finset.range k, a := by simp
  rw [he, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add, pow_mul]
  field_simp

/-- Denominator witness for the literal scalar families. -/
theorem eval_den_scalar (q a : RatFunc ℚ) (k : ℕ) (ha : a ≠ 0) :
    (den q k).eval a = a^k * GuoWang.paramDen q a k := by
  simpa only [den, GuoWang.paramDen, GuoWang.poch_eq_core] using
    eval_pairPoch_field q a 4 4 k ha

theorem eval_num_scalar (q a : RatFunc ℚ) (s w e k : ℕ) (ha : a ≠ 0) :
    (num q s w e k).eval a = a^k *
      ((-1)^k * (∑ j ∈ Finset.range (w*k+1), q^j) * q^e *
        (GuoWang.poch (a*q) (q^s) k * GuoWang.poch (q/a) (q^s) k *
          GuoWang.poch q (q^s) k)) := by
  rw [num, eval_mul, eval_C, eval_pairPoch_field q a 1 s k ha]
  simp only [pow_one, GuoWang.poch_eq_core]
  ring

/-- Replacing the inverse-a factors is a legal fraction identity. -/
theorem fraction_scalar (q a : RatFunc ℚ) (s w e k : ℕ) (ha : a ≠ 0) :
    (num q s w e k).eval a / (den q k).eval a =
      (-1)^k * (∑ j ∈ Finset.range (w*k+1), q^j) * q^e *
        (GuoWang.poch (a*q) (q^s) k * GuoWang.poch (q/a) (q^s) k *
          GuoWang.poch q (q^s) k) / GuoWang.paramDen q a k := by
  rw [eval_num_scalar q a s w e k ha, eval_den_scalar q a k ha]
  exact mul_div_mul_left _ _ (pow_ne_zero k ha)

#print axioms eval_pairPoch_field
#print axioms fraction_scalar
end
end GuoWang.Clear
```

### `GWClearSums.lean`

```lean
import GWClearProducts
import Mathlib.Algebra.BigOperators.Field

/-! A shared finite common numerator, with an exact fraction theorem. The common
denominator is used only where proved nonzero; no proper-divisor claim uses it. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

def commonDen (q : R) (N : ℕ) : Polynomial R :=
  ∏ k ∈ Finset.range N, den q k

def complement (q : R) (N k : ℕ) : Polynomial R :=
  ∏ i ∈ (Finset.range N).erase k, den q i

def commonNum (q : R) (N : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range N,
    (num q 2 6 (3*k^2) k - num q 4 8 (2*k^2+k) k) * complement q N k

@[simp] theorem map_commonDen (f : R →+* S) (q : R) (N : ℕ) :
    (commonDen q N).map f = commonDen (f q) N := by simp [commonDen, Polynomial.map_prod]

@[simp] theorem map_complement (f : R →+* S) (q : R) (N k : ℕ) :
    (complement q N k).map f = complement (f q) N k := by simp [complement, Polynomial.map_prod]

@[simp] theorem map_commonNum (f : R →+* S) (q : R) (N : ℕ) :
    (commonNum q N).map f = commonNum (f q) N := by simp [commonNum, Polynomial.map_sum]

theorem den_mul_complement (q : R) (N k : ℕ) (hk : k < N) :
    den q k * complement q N k = commonDen q N := by
  exact Finset.mul_prod_erase (Finset.range N) (fun i => den q i) (Finset.mem_range.mpr hk)

/-- Finite-sum division after proving every term's denominator nonzero. -/
theorem common_fraction {K : Type*} [Field K] (q a : K) (N : ℕ)
    (hd : ∀ k < N, (den q k).eval a ≠ 0) :
    (commonNum q N).eval a / (commonDen q N).eval a =
      (∑ k ∈ Finset.range N, (num q 2 6 (3*k^2) k).eval a / (den q k).eval a) -
      ∑ k ∈ Finset.range N, (num q 4 8 (2*k^2+k) k).eval a / (den q k).eval a := by
  have hC : (commonDen q N).eval a ≠ 0 := by
    simp only [commonDen, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k hk => hd k (Finset.mem_range.mp hk))
  rw [← Finset.sum_sub_distrib]
  simp only [commonNum, eval_finsetSum, eval_mul, eval_sub, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have he := congrArg (fun p : Polynomial K => p.eval a) (den_mul_complement q N k hk')
  rw [eval_mul] at he
  apply (div_eq_iff hC).mpr
  rw [← he]
  field_simp [hd k hk']

/-- The universal witness represents the review's literal scalar difference. -/
theorem common_fraction_D (q a : RatFunc ℚ) (N : ℕ) (ha : a ≠ 0)
    (hd : ∀ k < N, GuoWang.paramDen q a k ≠ 0) :
    (commonNum q N).eval a / (commonDen q N).eval a = GuoWang.D N q a := by
  rw [common_fraction]
  · simp only [fraction_scalar q a _ _ _ _ ha, GuoWang.D, GuoWang.A, GuoWang.B]
  · intro k hk
    rw [eval_den_scalar q a k ha]
    exact mul_ne_zero (pow_ne_zero k ha) (hd k hk)

/-- All specializations, including a->a*q^4, use this same ring map. -/
theorem specialize_fraction_D (f : R →+* RatFunc ℚ) (q : R) (a : RatFunc ℚ)
    (N : ℕ) (ha : a ≠ 0) (hd : ∀ k < N, GuoWang.paramDen (f q) a k ≠ 0) :
    Polynomial.eval₂ f a (commonNum q N) / Polynomial.eval₂ f a (commonDen q N) =
      GuoWang.D N (f q) a := by
  rw [← eval_map, ← eval_map, map_commonNum, map_commonDen]
  exact common_fraction_D (f q) a N ha hd

#print axioms common_fraction
#print axioms specialize_fraction_D
end
end GuoWang.Clear
```

### `GWClearSpecialize.lean`

```lean
import GWClearSums
import GWTerminatingDen

/-! Faithful two-variable polynomial model over ℚ[q], with legal parameter
specializations proved separately from zero tests of the numerator. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section

abbrev qMap : ℚ[X] →+* RatFunc ℚ := algebraMap _ _
def P (N : ℕ) : Polynomial ℚ[X] := commonNum (X : ℚ[X]) N
def H (N : ℕ) : Polynomial ℚ[X] := commonDen (X : ℚ[X]) N

def spec (a : RatFunc ℚ) : Polynomial ℚ[X] →+* RatFunc ℚ :=
  eval₂RingHom qMap a

@[simp] theorem at_P (N : ℕ) (a : RatFunc ℚ) :
    spec a (P N) = (commonNum GuoWang.X' N).eval a := by
  simp only [spec, coe_eval₂RingHom, P, ← eval_map, map_commonNum]
  rfl

@[simp] theorem at_H (N : ℕ) (a : RatFunc ℚ) :
    spec a (H N) = (commonDen GuoWang.X' N).eval a := by
  simp only [spec, coe_eval₂RingHom, H, ← eval_map, map_commonDen]
  rfl

/-- Exactly the same polynomial witness spec all admissible parameters. -/
theorem fraction_at (N : ℕ) (a : RatFunc ℚ) (ha : a ≠ 0)
    (hd : ∀ k < N, GuoWang.paramDen GuoWang.X' a k ≠ 0) :
    spec a (P N) / spec a (H N) = GuoWang.D N GuoWang.X' a := by
  rw [at_P, at_H]
  exact common_fraction_D _ _ _ ha hd

theorem at_H_ne_zero (N : ℕ) (a : RatFunc ℚ) (ha : a ≠ 0)
    (hd : ∀ k < N, GuoWang.paramDen GuoWang.X' a k ≠ 0) : spec a (H N) ≠ 0 := by
  rw [at_H]
  simp only [commonDen, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rw [eval_den_scalar _ _ _ ha]
  exact mul_ne_zero (pow_ne_zero k ha) (hd k (Finset.mem_range.mp hk))

theorem at_H_one_ne_zero (N : ℕ) : spec 1 (H N) ≠ 0 :=
  at_H_ne_zero N 1 one_ne_zero (fun k _ => GuoWang.paramDen_one_ne_zero k)

theorem fraction_one (N : ℕ) : spec 1 (P N) / spec 1 (H N) = GuoWang.diff N := by
  rw [fraction_at N 1 one_ne_zero (fun k _ => GuoWang.paramDen_one_ne_zero k), GuoWang.D_one]

theorem at_H_qpow_ne_zero (N e : ℕ) (he : e % 4 = 1) :
    spec (GuoWang.X'^e) (H N) ≠ 0 :=
  at_H_ne_zero N _ (pow_ne_zero e GuoWang.X'_ne_zero)
    (fun k _ => GuoWang.paramDen_qpow_ne_zero e k he)

theorem at_H_qpow_inv_ne_zero (N e : ℕ) (he : e % 4 = 1) :
    spec (GuoWang.X'^e)⁻¹ (H N) ≠ 0 :=
  at_H_ne_zero N _ (inv_ne_zero (pow_ne_zero e GuoWang.X'_ne_zero))
    (fun k _ => GuoWang.paramDen_qpow_inv_ne_zero e k he)

/-- An explicit numerator zero is equivalent to the rational zero, only after
legality of the specialization has been proved. -/
theorem at_P_eq_zero_iff (N : ℕ) (a : RatFunc ℚ) (ha : a ≠ 0)
    (hd : ∀ k < N, GuoWang.paramDen GuoWang.X' a k ≠ 0) :
    spec a (P N) = 0 ↔ GuoWang.D N GuoWang.X' a = 0 := by
  rw [← fraction_at N a ha hd, div_eq_zero_iff]
  simp only [at_H_ne_zero N a ha hd, or_false]

/-- The independently defined polynomial witness really has the initial root. -/
theorem at_P_q (N : ℕ) : spec GuoWang.X' (P N) = 0 := by
  exact (at_P_eq_zero_iff N _ GuoWang.X'_ne_zero
    (fun k _ => GuoWang.paramDen_q_ne_zero k)).mpr (GuoWang.D_at_q N)

/-- Ordinary-polynomial specialization spec a=1, before embedding into ℚ(q). -/
def Pone (N : ℕ) : ℚ[X] := (P N).eval 1
def Hone (N : ℕ) : ℚ[X] := (H N).eval 1

@[simp] theorem at_one (f : Polynomial ℚ[X]) :
    spec 1 f = qMap (f.eval 1) := by
  simpa only [spec, coe_eval₂RingHom, map_one] using (eval₂_at_apply (p := f) qMap 1)

theorem Hone_ne_zero (N : ℕ) : Hone N ≠ 0 := by
  intro h
  apply at_H_one_ne_zero N
  rw [at_one, show (H N).eval 1 = Hone N from rfl, h, map_zero]

theorem diff_fraction (N : ℕ) :
    GuoWang.diff N = qMap (Pone N) / qMap (Hone N) := by
  simpa only [at_one, Pone, Hone] using (fraction_one N).symm

#print axioms fraction_at
#print axioms at_H_one_ne_zero
#print axioms at_H_qpow_ne_zero
#print axioms at_H_qpow_inv_ne_zero
#print axioms at_P_eq_zero_iff
#print axioms at_P_q
#print axioms diff_fraction
end
end GuoWang.Clear
```

### `GWClearRoots.lean`

```lean
import GWClearSpecialize
import GWCyclotomic
import Mathlib.Algebra.Polynomial.Coeff

/-! Root tests for the actual two-variable numerator. The scalar root criterion
and separable-square argument are adapted from sibling GuoRoots/GuoAlgebra,
under new names; no sibling module is imported. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section

section RootTests
variable {K : Type*} [Field K] [CharZero K] {n : ℕ} {z : K}

theorem cyclotomic_dvd_iff_root (hn : 0 < n) (hz : IsPrimitiveRoot z n) (p : ℚ[X]) :
    cyclotomic n ℚ ∣ p ↔ aeval z p = 0 := by
  rw [cyclotomic_eq_minpoly_rat hz hn, minpoly.dvd_iff]

/-- One primitive-root test gives coefficientwise divisibility in ℚ[q][a]. -/
theorem C_cyclotomic_dvd_iff_map_zero (hn : 0 < n) (hz : IsPrimitiveRoot z n)
    (p : Polynomial ℚ[X]) :
    C (cyclotomic n ℚ) ∣ p ↔ p.map (aeval z).toRingHom = 0 := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h
    ext i
    rw [coeff_map, coeff_zero]
    exact (cyclotomic_dvd_iff_root hn hz _).mp (h i)
  · intro h i
    apply (cyclotomic_dvd_iff_root hn hz _).mpr
    have he := congrArg (fun p : Polynomial K => p.coeff i) h
    rw [coeff_map, coeff_zero] at he
    exact he

/-- The derivative criterion is algebraic, with the separability guard visible. -/
theorem square_dvd_from_derivative {F : Type*} [Field F] (p f : Polynomial F)
    (hp : IsCoprime p p.derivative) (hf : p ∣ f) (hdf : p ∣ f.derivative) : p^2 ∣ f := by
  obtain ⟨g, rfl⟩ := hf
  rw [derivative_mul] at hdf
  have hprod : p ∣ p.derivative * g := by
    have hs := dvd_sub hdf (dvd_mul_right p g.derivative)
    simpa only [add_sub_cancel_right] using hs
  obtain ⟨a, ha⟩ := hp.dvd_of_dvd_mul_left hprod
  refine ⟨a, ?_⟩
  rw [ha]
  ring

/-- It suffices to establish the two actual coefficient tests. This theorem
has explicit hypotheses and is not a proof of those tests for P n. -/
theorem C_cyclotomic_sq_dvd_of_coeff_roots (hn : 0 < n) (hz : IsPrimitiveRoot z n)
    (p : Polynomial ℚ[X]) (hv : p.map (aeval z).toRingHom = 0)
    (hd : ∀ i, aeval z (p.coeff i).derivative = 0) :
    C ((cyclotomic n ℚ)^2) ∣ p := by
  have : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  rw [C_dvd_iff_dvd_coeff]
  intro i
  apply square_dvd_from_derivative _ _ (separable_cyclotomic n ℚ)
  · exact (C_dvd_iff_dvd_coeff _ _).mp ((C_cyclotomic_dvd_iff_map_zero hn hz p).mpr hv) i
  · exact (cyclotomic_dvd_iff_root hn hz _).mpr (hd i)
end RootTests

/-- A polynomial denominator remains nonzero when q is a primitive root and
a remains an indeterminate. No denominator evaluation at a pole occurs. -/
theorem den_at_root_ne_zero {K : Type*} [Field K] {n : ℕ} {z : K}
    (hz : IsPrimitiveRoot z n) (h4 : n % 4 = 1) (k : ℕ) (hk : k < n) :
    den z k ≠ 0 := by
  have hc : n.Coprime 4 := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm n 4, Nat.gcd_rec, h4]
    decide
  unfold den pairPoch
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hnj : ¬ n ∣ 4+4*j := by
    intro hd
    have hd' : n ∣ 4*(j+1) := by convert hd using 1; omega
    have hjn := hc.dvd_mul_left.mp hd'
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by have := Finset.mem_range.mp hj; omega)) hjn
  have hv : 1-z^(4+4*j) ≠ 0 := by
    intro he
    exact hnj ((hz.pow_eq_one_iff_dvd _).mp (sub_eq_zero.mp he).symm)
  have hl : (1-X*C (z^(4+4*j)) : Polynomial K) ≠ 0 := by
    intro he
    have := congrArg (fun p : Polynomial K => p.eval 0) he
    simp at this
  exact mul_ne_zero (mul_ne_zero hl (monic_X_sub_C _).ne_zero) (C_ne_zero.mpr hv)

theorem H_at_root_ne_zero {K : Type*} [Field K] [CharZero K] {n : ℕ} {z : K}
    (hz : IsPrimitiveRoot z n) (h4 : n % 4 = 1) : (H n).map (aeval z).toRingHom ≠ 0 := by
  rw [H, map_commonDen]
  rw [show (aeval z).toRingHom (X : ℚ[X]) = z from Polynomial.aeval_X z]
  unfold commonDen
  exact Finset.prod_ne_zero_iff.mpr (fun k hk => den_at_root_ne_zero hz h4 k (Finset.mem_range.mp hk))

/-- Generic-parameter zero in K(a) is precisely the numerator map zero, with
the actual root denominator proved nonzero. -/
theorem P_at_root_zero_iff {K : Type*} [Field K] [CharZero K] {n : ℕ} {z : K}
    (hz : IsPrimitiveRoot z n) (h4 : n % 4 = 1) :
    (algebraMap (Polynomial K) (RatFunc K) ((P n).map (aeval z).toRingHom) /
      algebraMap (Polynomial K) (RatFunc K) ((H n).map (aeval z).toRingHom) = 0) ↔
      (P n).map (aeval z).toRingHom = 0 := by
  rw [div_eq_zero_iff]
  have hd := RatFunc.algebraMap_ne_zero (H_at_root_ne_zero hz h4)
  simp only [hd, or_false]
  constructor
  · intro he
    exact RatFunc.algebraMap_injective K (he.trans (map_zero _).symm)
  · intro he
    rw [he, map_zero]

#print axioms C_cyclotomic_dvd_iff_map_zero
#print axioms C_cyclotomic_sq_dvd_of_coeff_roots
#print axioms H_at_root_ne_zero
#print axioms P_at_root_zero_iff
end
end GuoWang.Clear
```

### `GWClearTop.lean`

```lean
import GWClearRoots

/-! The top cyclotomic bridge uses the actual numerator and nonzero ordinary
polynomial denominator from the explicit two-variable model. It deliberately
makes no assertion that this common denominator is a unit at proper divisors. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section

/-- The a=1 denominator, as an ordinary finite product over the coefficient ring. -/
theorem den_eval_one {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    (den q k).eval 1 = (∏ j ∈ Finset.range k, (1-q^(4*(j+1))))^3 := by
  rw [den, eval_pairPoch, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [show 4+4*j = 4*(j+1) by omega]
  simp only [one_mul]
  ring

theorem Hone_eq (N : ℕ) : Hone N = ∏ k ∈ Finset.range N, GuoWang.denPoly k ^ 3 := by
  simp only [Hone, H, commonDen, eval_prod, den_eval_one, GuoWang.denPoly]

theorem coprime_Hone_top (n : ℕ) (h4 : n % 4 = 1) (e : ℕ) :
    IsCoprime ((cyclotomic n ℚ)^e) (Hone n) := by
  rw [Hone_eq]
  apply IsCoprime.prod_right_iff.mpr
  intro k hk
  exact ((GuoWang.coprime_denPoly_top n k h4 (Finset.mem_range.mp hk)).pow_right).pow_left

/-- Exact reduced-numerator equivalence for every cyclotomic exponent, without
adding denominator assumptions to the eventual source endpoint. -/
theorem top_reduced_num_iff (n : ℕ) (h4 : n % 4 = 1) (e : ℕ) :
    (cyclotomic n ℚ)^e ∣ (GuoWang.diff n).num ↔
      (cyclotomic n ℚ)^e ∣ Pone n := by
  exact GuoWang.modulus_dvd_reduced_num_iff _ _ _ _ (Hone_ne_zero n)
    (diff_fraction n) (coprime_Hone_top n h4 e)

/-- A coefficientwise factor really specializes to the corresponding factor in
the polynomial numerator at a=1. -/
theorem Pone_dvd_of_C_dvd (N : ℕ) (f : ℚ[X]) (h : C f ∣ P N) : f ∣ Pone N := by
  simpa only [Pone, eval_C] using Polynomial.eval_dvd (x := (1:ℚ[X])) h

#print axioms Hone_eq
#print axioms coprime_Hone_top
#print axioms top_reduced_num_iff
#print axioms Pone_dvd_of_C_dvd
end
end GuoWang.Clear
```

### `GWClearShift.lean`

```lean
import GWClearRoots

/-! One rescaling endomorphism for every parameter shift. The inverse and map
laws justify preservation of generic-root denominator regularity. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

def rescale (u : R) : Polynomial R →+* Polynomial R := compRingHom (X*C u)

@[simp] theorem rescale_apply (u : R) (p : Polynomial R) :
    rescale u p = p.comp (X*C u) := rfl

@[simp] theorem rescale_C (u c : R) : rescale u (C c) = C c := by simp

@[simp] theorem map_rescale (f : R →+* S) (u : R) (p : Polynomial R) :
    (rescale u p).map f = rescale (f u) (p.map f) := by simp [map_comp]

@[simp] theorem eval_rescale (u a : R) (p : Polynomial R) :
    (rescale u p).eval a = p.eval (a*u) := by
  rw [rescale_apply, eval_comp]
  simp only [eval_mul, eval_X, eval_C]

theorem eval₂_rescale (f : R →+* S) (u : R) (a : S) (p : Polynomial R) :
    eval₂ f a (rescale u p) = eval₂ f (a*f u) p := by
  rw [← eval_map, map_rescale, eval_rescale, eval_map]

/-- An a-independent factor commutes with the parameter shift. This is the
algebraic prerequisite for applying the first-order cyclic step twice. -/
theorem rescale_C_mul (u c : R) (p : Polynomial R) :
    rescale u (C c*p) = C c*rescale u p := by rw [map_mul, rescale_C]

section Field
variable {K : Type*} [Field K]

theorem rescale_inverse (u : K) (hu : u ≠ 0) (p : Polynomial K) :
    rescale u⁻¹ (rescale u p) = p := by
  simp only [rescale_apply, comp_assoc, mul_comp, X_comp, C_comp]
  rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, mul_one, comp_X]

theorem rescale_injective (u : K) (hu : u ≠ 0) : Function.Injective (rescale u) := by
  intro p r h
  have he := congrArg (rescale u⁻¹) h
  simpa only [rescale_inverse u hu] using he

theorem rescale_ne_zero (u : K) (hu : u ≠ 0) (p : Polynomial K) (hp : p ≠ 0) :
    rescale u p ≠ 0 := by
  intro he
  apply hp
  exact rescale_injective u hu (he.trans (map_zero (rescale u)).symm)
end Field

/-- The generic independent-parameter root denominator stays nonzero after
any number of a->a*q^4 shifts. -/
theorem shifted_H_at_root_ne_zero {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {z : K} (hn : 0 < n) (hz : IsPrimitiveRoot z n) (h4 : n % 4 = 1)
    (j : ℕ) : ((rescale ((X : ℚ[X])^(4*j)) (H n)).map (aeval z).toRingHom) ≠ 0 := by
  rw [map_rescale]
  exact rescale_ne_zero _ (by simpa using pow_ne_zero (4*j) (hz.ne_zero hn.ne'))
    _ (H_at_root_ne_zero hz h4)

#print axioms eval₂_rescale
#print axioms rescale_C_mul
#print axioms rescale_injective
#print axioms shifted_H_at_root_ne_zero
end
end GuoWang.Clear
```

### `GWClearSteps.lean`

```lean
import GWClearSums

/-! Shared actual finite-product successor ratios. No cancellation of the
numerator Pochhammer product is used, so terminating numerators are allowed. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

def factor (q : R) (t s k : ℕ) : Polynomial R :=
  (1-X*C (q^(t+s*k))) * (X-C (q^(t+s*k))) * C (1-q^(t+s*k))

theorem pairPoch_succ (q : R) (t s k : ℕ) :
    pairPoch q t s (k+1) = pairPoch q t s k * factor q t s k := by
  exact Finset.prod_range_succ _ _

theorem den_succ (q : R) (k : ℕ) : den q (k+1) = den q k * factor q 4 4 k :=
  pairPoch_succ q 4 4 k

/-- q-power and q-integer changes are kept scalar so the same lemma serves
both the bibasic and ordinary-base families. -/
theorem num_succ_cross (q : R) (s w e d k : ℕ) :
    num q s w (e+d) (k+1) * C (∑ j ∈ Finset.range (w*k+1), q^j) =
      -C ((∑ j ∈ Finset.range (w*(k+1)+1), q^j)*q^d) *
        num q s w e k * factor q 1 s k := by
  simp only [num, pairPoch_succ, pow_succ (-1:R), pow_add]
  simp only [map_mul, map_neg, map_one]
  ring

section Field
variable {K : Type*} [Field K]

def term (q a : K) (s w e k : ℕ) : K :=
  (num q s w e k).eval a / (den q k).eval a

/-- A legal next-term ratio for the literal finite products; no hypothesis
requires the current numerator or the next numerator to be nonzero. -/
theorem term_succ (q a : K) (s w e d k : ℕ)
    (hi : (∑ j ∈ Finset.range (w*k+1), q^j) ≠ 0)
    (hd : (den q k).eval a ≠ 0) (hf : (factor q 4 4 k).eval a ≠ 0) :
    term q a s w (e+d) (k+1) =
      (-(∑ j ∈ Finset.range (w*(k+1)+1), q^j) * q^d /
        (∑ j ∈ Finset.range (w*k+1), q^j) *
        (factor q 1 s k).eval a / (factor q 4 4 k).eval a) * term q a s w e k := by
  have hn := congrArg (fun p : Polynomial K => p.eval a) (num_succ_cross q s w e d k)
  simp only [eval_mul, eval_C, eval_neg] at hn
  have hnum : (num q s w (e+d) (k+1)).eval a =
      (-(∑ j ∈ Finset.range (w*(k+1)+1), q^j)*q^d) *
        (num q s w e k).eval a * (factor q 1 s k).eval a /
        (∑ j ∈ Finset.range (w*k+1), q^j) := by
    apply (eq_div_iff hi).mpr
    simpa only [neg_mul] using hn
  simp only [term, hnum, den_succ, eval_mul]
  field_simp

/-- Denominator of this next-term formula is legal whenever the actual two
successive denominators are legal. -/
theorem factor_den_ne_zero (q a : K) (k : ℕ) (hd : (den q (k+1)).eval a ≠ 0) :
    (factor q 4 4 k).eval a ≠ 0 := by
  rw [den_succ, eval_mul] at hd
  exact (mul_ne_zero_iff.mp hd).2
end Field

/-- The generic successor model specializes to the actual endpoint families. -/
theorem term_A (q a : RatFunc ℚ) (k : ℕ) (ha : a ≠ 0) :
    term q a 2 6 (3*k^2) k = GuoWang.A q a k := fraction_scalar q a 2 6 _ k ha

theorem term_B (q a : RatFunc ℚ) (k : ℕ) (ha : a ≠ 0) :
    term q a 4 8 (2*k^2+k) k = GuoWang.B q a k := fraction_scalar q a 4 8 _ k ha

#print axioms num_succ_cross
#print axioms term_succ
#print axioms term_A
#print axioms term_B
end
end GuoWang.Clear
```

### `GWScalarNext.lean`

```lean
import GWClearSteps
import GWRationalA

/-! The actual scalar finite-product next ratios, with every denominator
legality explicit. Zero numerator factors are never cancelled. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section

lemma eval_factor_field {K : Type*} [Field K] (q a : K) (t s k : ℕ) (ha : a ≠ 0) :
    (factor q t s k).eval a =
      a*((1-a*q^(t+s*k))*(1-q^(t+s*k)/a)*(1-q^(t+s*k))) := by
  simp only [factor, eval_mul, eval_sub, eval_one, eval_X, eval_C]
  field_simp

lemma qInt_ne_zero (m : ℕ) (hm : 0 < m) : GuoWang.qInt m ≠ 0 := by
  rw [GuoWang.qInt_source]
  exact div_ne_zero (GuoWang.one_sub_X'_pow_ne_zero m hm)
    (by simpa only [pow_one] using GuoWang.one_sub_X'_pow_ne_zero 1 (by omega))

lemma scalar_step_den (a : RatFunc ℚ) (ha : a ≠ 0) (k : ℕ)
    (hd : GuoWang.paramDen GuoWang.X' a k ≠ 0) :
    (den GuoWang.X' k).eval a ≠ 0 := by
  rw [eval_den_scalar _ _ _ ha]
  exact mul_ne_zero (pow_ne_zero k ha) hd

theorem A_next_factor (a : RatFunc ℚ) (ha : a ≠ 0) (k : ℕ)
    (hd : GuoWang.paramDen GuoWang.X' a k ≠ 0)
    (hd' : GuoWang.paramDen GuoWang.X' a (k+1) ≠ 0) :
    GuoWang.A GuoWang.X' a (k+1) =
      (-GuoWang.qInt (6*(k+1)+1)*GuoWang.X'^(6*k+3)/GuoWang.qInt (6*k+1) *
        (factor GuoWang.X' 1 2 k).eval a / (factor GuoWang.X' 4 4 k).eval a) *
        GuoWang.A GuoWang.X' a k := by
  have hi : (∑ j ∈ Finset.range (6*k+1), GuoWang.X'^j) ≠ 0 := by
    rw [← GuoWang.qInt_eq_sum]
    exact qInt_ne_zero _ (by omega)
  have h := term_succ GuoWang.X' a 2 6 (3*k^2) (6*k+3) k hi
    (scalar_step_den a ha k hd) (factor_den_ne_zero _ _ k (scalar_step_den a ha (k+1) hd'))
  rw [show 3*k^2+(6*k+3) = 3*(k+1)^2 by ring] at h
  simpa only [term_A _ _ _ ha, ← GuoWang.qInt_eq_sum] using h

theorem B_next_factor (a : RatFunc ℚ) (ha : a ≠ 0) (k : ℕ)
    (hd : GuoWang.paramDen GuoWang.X' a k ≠ 0)
    (hd' : GuoWang.paramDen GuoWang.X' a (k+1) ≠ 0) :
    GuoWang.B GuoWang.X' a (k+1) =
      (-GuoWang.qInt (8*(k+1)+1)*GuoWang.X'^(4*k+3)/GuoWang.qInt (8*k+1) *
        (factor GuoWang.X' 1 4 k).eval a / (factor GuoWang.X' 4 4 k).eval a) *
        GuoWang.B GuoWang.X' a k := by
  have hi : (∑ j ∈ Finset.range (8*k+1), GuoWang.X'^j) ≠ 0 := by
    rw [← GuoWang.qInt_eq_sum]
    exact qInt_ne_zero _ (by omega)
  have h := term_succ GuoWang.X' a 4 8 (2*k^2+k) (4*k+3) k hi
    (scalar_step_den a ha k hd) (factor_den_ne_zero _ _ k (scalar_step_den a ha (k+1) hd'))
  rw [show 2*k^2+k+(4*k+3) = 2*(k+1)^2+(k+1) by ring] at h
  simpa only [term_B _ _ _ ha, ← GuoWang.qInt_eq_sum] using h

#print axioms A_next_factor
#print axioms B_next_factor
end
end GuoWang.Clear
```

### `GWNormalizedNext.lean`

```lean
import GWScalarNext

/-! Connecting the literal summands to the normalized next ratios. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section
open GuoWang

lemma factor_ratio (q a : RatFunc ℚ) (s k : ℕ) (ha : a ≠ 0) :
    (factor q 1 s k).eval a / (factor q 4 4 k).eval a =
      ((1-a*q^(1+s*k))*(1-q^(1+s*k)/a)*(1-q^(1+s*k))) /
        ((1-a*q^(4+4*k))*(1-q^(4+4*k)/a)*(1-q^(4+4*k))) := by
  rw [eval_factor_field _ _ _ _ _ ha, eval_factor_field _ _ _ _ _ ha]
  exact mul_div_mul_left _ _ ha

lemma qInt_quotient (r t : ℕ) :
    qInt r / qInt t = (1-X'^r)/(1-X'^t) := by
  rw [qInt_source, qInt_source]
  exact div_div_div_cancel_right₀ (by simpa only [pow_one] using one_sub_X'_pow_ne_zero 1 (by omega)) _ _

theorem A_next (a : RatFunc ℚ) (ha : a ≠ 0) (k : ℕ)
    (hd : paramDen X' a k ≠ 0) (hd' : paramDen X' a (k+1) ≠ 0) :
    A X' a (k+1) = WZ.nextA X' a (X'^(2*k)) * A X' a k := by
  rw [A_next_factor a ha k hd hd']
  congr 1
  calc
    _ = -(qInt (6*(k+1)+1)/qInt (6*k+1))*X'^(6*k+3) *
        ((factor X' 1 2 k).eval a / (factor X' 4 4 k).eval a) := by ring
    _ = _ := by
      rw [qInt_quotient, factor_ratio _ _ _ _ ha]
      have e₁ : X'^(6*(k+1)+1) = X'^7*(X'^(2*k))^3 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e₂ : X'^(6*k+1) = X'*(X'^(2*k))^3 := by
        rw [← pow_mul, ← pow_succ']; congr 1; omega
      have e₃ : X'^(6*k+3) = X'^3*(X'^(2*k))^3 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e₄ : X'^(1+2*k) = X'*X'^(2*k) := by rw [pow_add, pow_one]
      have e₅ : X'^(4+4*k) = X'^4*(X'^(2*k))^2 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      rw [e₁, e₂, e₃, e₄, e₅]
      unfold WZ.nextA
      ring

theorem B_next (a : RatFunc ℚ) (ha : a ≠ 0) (k : ℕ)
    (hd : paramDen X' a k ≠ 0) (hd' : paramDen X' a (k+1) ≠ 0) :
    B X' a (k+1) = WZ.nextB X' a (X'^(4*k)) * B X' a k := by
  rw [B_next_factor a ha k hd hd']
  congr 1
  calc
    _ = -(qInt (8*(k+1)+1)/qInt (8*k+1))*X'^(4*k+3) *
        ((factor X' 1 4 k).eval a / (factor X' 4 4 k).eval a) := by ring
    _ = _ := by
      rw [qInt_quotient, factor_ratio _ _ _ _ ha]
      have e₁ : X'^(8*(k+1)+1) = X'^9*(X'^(4*k))^2 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e₂ : X'^(8*k+1) = X'*(X'^(4*k))^2 := by
        rw [← pow_mul, ← pow_succ']; congr 1; omega
      have e₃ : X'^(4*k+3) = X'^3*X'^(4*k) := by rw [← pow_add]; congr 1; omega
      have e₄ : X'^(1+4*k) = X'*X'^(4*k) := by rw [pow_add, pow_one]
      rw [e₁, e₂, e₃, e₄, pow_add X' 4 (4*k)]
      unfold WZ.nextB
      ring

#print axioms A_next
#print axioms B_next
end
end GuoWang.Clear
```

### `GWAuditR2.lean`

```lean
import GWClearProducts
import GWClearSums
import GWClearSpecialize
import GWClearRoots
import GWClearTop
import GWClearShift
import GWClearSteps
import GWScalarNext
import GWNormalizedNext
import GWAudit

/-! Exact stage-2 theorem types and transitive axioms. -/
#eval Lean.versionString
#print GuoWang.Conjecture41
#check @GuoWang.guo_wang_conj_4_1_one
#print axioms GuoWang.guo_wang_conj_4_1_one
#check @GuoWang.Clear.map_pairPoch
#print axioms GuoWang.Clear.map_pairPoch
#check @GuoWang.Clear.map_den
#print axioms GuoWang.Clear.map_den
#check @GuoWang.Clear.map_num
#print axioms GuoWang.Clear.map_num
#check @GuoWang.Clear.eval_pairPoch
#print axioms GuoWang.Clear.eval_pairPoch
#check @GuoWang.Clear.eval_pairPoch_field
#print axioms GuoWang.Clear.eval_pairPoch_field
#check @GuoWang.Clear.eval_den_scalar
#print axioms GuoWang.Clear.eval_den_scalar
#check @GuoWang.Clear.eval_num_scalar
#print axioms GuoWang.Clear.eval_num_scalar
#check @GuoWang.Clear.fraction_scalar
#print axioms GuoWang.Clear.fraction_scalar
#check @GuoWang.Clear.map_commonDen
#print axioms GuoWang.Clear.map_commonDen
#check @GuoWang.Clear.map_complement
#print axioms GuoWang.Clear.map_complement
#check @GuoWang.Clear.map_commonNum
#print axioms GuoWang.Clear.map_commonNum
#check @GuoWang.Clear.den_mul_complement
#print axioms GuoWang.Clear.den_mul_complement
#check @GuoWang.Clear.common_fraction
#print axioms GuoWang.Clear.common_fraction
#check @GuoWang.Clear.common_fraction_D
#print axioms GuoWang.Clear.common_fraction_D
#check @GuoWang.Clear.specialize_fraction_D
#print axioms GuoWang.Clear.specialize_fraction_D
#check @GuoWang.Clear.at_P
#print axioms GuoWang.Clear.at_P
#check @GuoWang.Clear.at_H
#print axioms GuoWang.Clear.at_H
#check @GuoWang.Clear.fraction_at
#print axioms GuoWang.Clear.fraction_at
#check @GuoWang.Clear.at_H_ne_zero
#print axioms GuoWang.Clear.at_H_ne_zero
#check @GuoWang.Clear.at_H_one_ne_zero
#print axioms GuoWang.Clear.at_H_one_ne_zero
#check @GuoWang.Clear.fraction_one
#print axioms GuoWang.Clear.fraction_one
#check @GuoWang.Clear.at_H_qpow_ne_zero
#print axioms GuoWang.Clear.at_H_qpow_ne_zero
#check @GuoWang.Clear.at_H_qpow_inv_ne_zero
#print axioms GuoWang.Clear.at_H_qpow_inv_ne_zero
#check @GuoWang.Clear.at_P_eq_zero_iff
#print axioms GuoWang.Clear.at_P_eq_zero_iff
#check @GuoWang.Clear.at_P_q
#print axioms GuoWang.Clear.at_P_q
#check @GuoWang.Clear.at_one
#print axioms GuoWang.Clear.at_one
#check @GuoWang.Clear.Hone_ne_zero
#print axioms GuoWang.Clear.Hone_ne_zero
#check @GuoWang.Clear.diff_fraction
#print axioms GuoWang.Clear.diff_fraction
#check @GuoWang.Clear.cyclotomic_dvd_iff_root
#print axioms GuoWang.Clear.cyclotomic_dvd_iff_root
#check @GuoWang.Clear.C_cyclotomic_dvd_iff_map_zero
#print axioms GuoWang.Clear.C_cyclotomic_dvd_iff_map_zero
#check @GuoWang.Clear.square_dvd_from_derivative
#print axioms GuoWang.Clear.square_dvd_from_derivative
#check @GuoWang.Clear.C_cyclotomic_sq_dvd_of_coeff_roots
#print axioms GuoWang.Clear.C_cyclotomic_sq_dvd_of_coeff_roots
#check @GuoWang.Clear.den_at_root_ne_zero
#print axioms GuoWang.Clear.den_at_root_ne_zero
#check @GuoWang.Clear.H_at_root_ne_zero
#print axioms GuoWang.Clear.H_at_root_ne_zero
#check @GuoWang.Clear.P_at_root_zero_iff
#print axioms GuoWang.Clear.P_at_root_zero_iff
#check @GuoWang.Clear.den_eval_one
#print axioms GuoWang.Clear.den_eval_one
#check @GuoWang.Clear.Hone_eq
#print axioms GuoWang.Clear.Hone_eq
#check @GuoWang.Clear.coprime_Hone_top
#print axioms GuoWang.Clear.coprime_Hone_top
#check @GuoWang.Clear.top_reduced_num_iff
#print axioms GuoWang.Clear.top_reduced_num_iff
#check @GuoWang.Clear.Pone_dvd_of_C_dvd
#print axioms GuoWang.Clear.Pone_dvd_of_C_dvd
#check @GuoWang.Clear.rescale_apply
#print axioms GuoWang.Clear.rescale_apply
#check @GuoWang.Clear.rescale_C
#print axioms GuoWang.Clear.rescale_C
#check @GuoWang.Clear.map_rescale
#print axioms GuoWang.Clear.map_rescale
#check @GuoWang.Clear.eval_rescale
#print axioms GuoWang.Clear.eval_rescale
#check @GuoWang.Clear.eval₂_rescale
#print axioms GuoWang.Clear.eval₂_rescale
#check @GuoWang.Clear.rescale_C_mul
#print axioms GuoWang.Clear.rescale_C_mul
#check @GuoWang.Clear.rescale_inverse
#print axioms GuoWang.Clear.rescale_inverse
#check @GuoWang.Clear.rescale_injective
#print axioms GuoWang.Clear.rescale_injective
#check @GuoWang.Clear.rescale_ne_zero
#print axioms GuoWang.Clear.rescale_ne_zero
#check @GuoWang.Clear.shifted_H_at_root_ne_zero
#print axioms GuoWang.Clear.shifted_H_at_root_ne_zero
#check @GuoWang.Clear.pairPoch_succ
#print axioms GuoWang.Clear.pairPoch_succ
#check @GuoWang.Clear.den_succ
#print axioms GuoWang.Clear.den_succ
#check @GuoWang.Clear.num_succ_cross
#print axioms GuoWang.Clear.num_succ_cross
#check @GuoWang.Clear.term_succ
#print axioms GuoWang.Clear.term_succ
#check @GuoWang.Clear.factor_den_ne_zero
#print axioms GuoWang.Clear.factor_den_ne_zero
#check @GuoWang.Clear.term_A
#print axioms GuoWang.Clear.term_A
#check @GuoWang.Clear.term_B
#print axioms GuoWang.Clear.term_B
#check @GuoWang.Clear.eval_factor_field
#print axioms GuoWang.Clear.eval_factor_field
#check @GuoWang.Clear.qInt_ne_zero
#print axioms GuoWang.Clear.qInt_ne_zero
#check @GuoWang.Clear.scalar_step_den
#print axioms GuoWang.Clear.scalar_step_den
#check @GuoWang.Clear.A_next_factor
#print axioms GuoWang.Clear.A_next_factor
#check @GuoWang.Clear.B_next_factor
#print axioms GuoWang.Clear.B_next_factor
#check @GuoWang.Clear.factor_ratio
#print axioms GuoWang.Clear.factor_ratio
#check @GuoWang.Clear.qInt_quotient
#print axioms GuoWang.Clear.qInt_quotient
#check @GuoWang.Clear.A_next
#print axioms GuoWang.Clear.A_next
#check @GuoWang.Clear.B_next
#print axioms GuoWang.Clear.B_next
```

### `GWShiftProducts.lean`

```lean
import GWProductRatios
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Actual parameter shifts, shared between the two finite-product families.
All formulae are in an arbitrary field. Numerator products may vanish. -/
namespace GuoWang.WZ
open QWZCore
variable {K : Type*} [Field K]

lemma poch_backward_two_ratio (z b : K) (k : ℕ) (hb : b ≠ 0)
    (h₁ : 1-z/b^2*b^k ≠ 0) (h₂ : 1-z/b^2*b^(k+1) ≠ 0) :
    poch (z/b^2) b k = poch z b k*(1-z/b^2)*(1-z/b)/
      ((1-z/b^2*b^k)*(1-z/b^2*b^(k+1))) := by
  have h := poch_shift_two (z/b^2) b k
  rw [div_mul_cancel₀ z (pow_ne_zero 2 hb)] at h
  have he : z/b^2*b = z/b := by field_simp
  rw [he] at h
  apply (eq_div_iff (mul_ne_zero h₁ h₂)).mpr
  calc
    _ = (1-z/b^2*b^k)*(1-z/b^2*b^(k+1))*poch (z/b^2) b k := by ring
    _ = _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Pair of a and a^{-1} factors. -/
def pair (q a : K) (t s k : ℕ) : K := poch (a*q^t) (q^s) k * poch (q^t/a) (q^s) k

lemma pair_shift_two (q a : K) (k : ℕ) (hq : q ≠ 0) (ha : a ≠ 0)
    (h₁ : 1-a*q ≠ 0) (h₃ : 1-a*q^3 ≠ 0)
    (hx₁ : a*q-q^(2*k) ≠ 0) (hx₃ : a*q^3-q^(2*k) ≠ 0) :
    pair q (a*q^4) 1 2 k = pair q a 1 2 k *
      ((1-a*q*q^(2*k))*(1-a*q^3*q^(2*k)))/
      ((a*q^3-q^(2*k))*(a*q-q^(2*k))) := by
  have e₁ : a*q^4*q^1 = (a*q)*(q^2)^2 := by ring
  have e₂ : q^1/(a*q^4) = (q/a)/(q^2)^2 := by field_simp
  have e₃ : (a*q)*(q^2)^k = a*q*q^(2*k) := by rw [← pow_mul]
  have e₄ : (a*q)*(q^2)^(k+1) = a*q^3*q^(2*k) := by rw [pow_succ]; ring
  have e₅ : 1-(q/a)/(q^2)^2*(q^2)^k = (a*q^3-q^(2*k))/(a*q^3) := by
    simp only [← pow_mul]
    field_simp [ha, hq]
    ring
  have e₆ : 1-(q/a)/(q^2)^2*(q^2)^(k+1) = (a*q-q^(2*k))/(a*q) := by
    rw [pow_succ (q^2) k]
    simp only [← pow_mul]
    field_simp [ha, hq]
    ring
  have ez₁ : 1-(q/a)/(q^2)^2*(q^2)^k ≠ 0 := by
    rw [e₅]; exact div_ne_zero hx₃ (mul_ne_zero ha (pow_ne_zero 3 hq))
  have ez₂ : 1-(q/a)/(q^2)^2*(q^2)^(k+1) ≠ 0 := by
    rw [e₆]; exact div_ne_zero hx₁ (mul_ne_zero ha hq)
  have e₇ : 1-(a*q)*q^2 = 1-a*q^3 := by ring
  unfold pair
  rw [e₁, e₂, poch_forward_two_ratio (a*q) (q^2) k h₁ (by rw [e₇]; exact h₃),
    poch_backward_two_ratio (q/a) (q^2) k (pow_ne_zero 2 hq) ez₁ ez₂]
  simp only [pow_one]
  rw [e₃, e₄, e₅, e₆, e₇]
  field_simp [ha, hq, h₁, h₃, hx₁, hx₃]
  ring

lemma pair_shift_four (q a : K) (k : ℕ) (hq : q ≠ 0) (ha : a ≠ 0)
    (h₁ : 1-a*q ≠ 0) (hx₃ : a*q^3-q^(4*k) ≠ 0) :
    pair q (a*q^4) 1 4 k = pair q a 1 4 k *
      (-(1-a*q^3)*(1-a*q*q^(4*k)))/((1-a*q)*(a*q^3-q^(4*k))) := by
  have e₁ : a*q^4*q^1 = (a*q)*q^4 := by ring
  have e₂ : q^1/(a*q^4) = (q/a)/q^4 := by field_simp
  have e₃ : 1-(q/a)/q^4*(q^4)^k = (a*q^3-q^(4*k))/(a*q^3) := by
    simp only [← pow_mul]
    field_simp [ha, hq]
  have ez : 1-(q/a)/q^4*(q^4)^k ≠ 0 := by
    rw [e₃]; exact div_ne_zero hx₃ (mul_ne_zero ha (pow_ne_zero 3 hq))
  unfold pair
  rw [e₁, e₂, poch_forward_ratio (a*q) (q^4) k h₁,
    poch_backward_ratio (q/a) (q^4) k (pow_ne_zero 4 hq) ez, e₃]
  simp only [pow_one, ← pow_mul]
  field_simp [ha, hq, h₁, hx₃]
  ring

lemma pair_den_shift (q a : K) (k : ℕ) (hq : q ≠ 0) (ha : a ≠ 0)
    (h₄ : 1-a*q^4 ≠ 0) (hx : 1-q^(4*k)/a ≠ 0) :
    pair q (a*q^4) 4 4 k = pair q a 4 4 k *
      ((1-a*q^4*q^(4*k))*(1-a⁻¹))/((1-a*q^4)*(1-q^(4*k)/a)) := by
  have e₁ : a*q^4*q^4 = (a*q^4)*q^4 := by ring
  have e₂ : q^4/(a*q^4) = (q^4/a)/q^4 := by field_simp
  have e₃ : (q^4/a)/q^4 = a⁻¹ := by field_simp
  have ez : 1-(q^4/a)/q^4*(q^4)^k ≠ 0 := by
    rw [e₃, ← pow_mul]
    simpa only [div_eq_mul_inv, mul_comm] using hx
  unfold pair
  rw [e₁, e₂, poch_forward_ratio (a*q^4) (q^4) k h₄,
    poch_backward_ratio (q^4/a) (q^4) k (pow_ne_zero 4 hq) ez, e₃]
  simp only [← pow_mul]
  field_simp [ha, hq, h₄, hx]

#print axioms pair_shift_two
#print axioms pair_shift_four
#print axioms pair_den_shift
end GuoWang.WZ
```

### `GWFieldTerms.lean`

```lean
import GWClearSteps
import GWShiftProducts
import GWRationalA

/-! One field-valued finite-product model for both families. -/
namespace GuoWang.WZ
open QWZCore
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

def pd (q a : K) (k : ℕ) : K := pair q a 4 4 k * QWZCore.poch (q^4) (q^4) k

def ft (q a : K) (s w e k : ℕ) : K :=
  (-1)^k * (∑ j ∈ Finset.range (w*k+1), q^j) * q^e *
    (pair q a 1 s k * QWZCore.poch q (q^s) k) / pd q a k

lemma ft_eq_term (q a : K) (s w e k : ℕ) (ha : a ≠ 0) :
    ft q a s w e k = GuoWang.Clear.term q a s w e k := by
  unfold GuoWang.Clear.term GuoWang.Clear.num GuoWang.Clear.den
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    GuoWang.Clear.eval_pairPoch_field q a 1 s k ha,
    GuoWang.Clear.eval_pairPoch_field q a 4 4 k ha]
  simp only [pow_one]
  unfold ft pd pair
  rw [show (-1)^k * (∑ j ∈ Finset.range (w*k+1), q^j) * q^e *
      (a^k * (QWZCore.poch (a*q) (q^s) k * QWZCore.poch (q/a) (q^s) k * QWZCore.poch q (q^s) k)) =
      a^k * ((-1)^k * (∑ j ∈ Finset.range (w*k+1), q^j) * q^e *
      (QWZCore.poch (a*q) (q^s) k * QWZCore.poch (q/a) (q^s) k * QWZCore.poch q (q^s) k)) by ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero k ha)]
  simp only [pow_one]

lemma pd_shift (q a : K) (k : ℕ) (hq : q ≠ 0) (ha : a ≠ 0)
    (h₄ : 1-a*q^4 ≠ 0) (hx : 1-q^(4*k)/a ≠ 0) :
    pd q (a*q^4) k = pd q a k *
      ((1-a*q^4*q^(4*k))*(1-a⁻¹))/((1-a*q^4)*(1-q^(4*k)/a)) := by
  unfold pd
  rw [pair_den_shift q a k hq ha h₄ hx]
  ring

#print axioms ft_eq_term
#print axioms pd_shift
end
end GuoWang.WZ
```

### `GWFieldShiftA.lean`

```lean
import GWFieldTerms

namespace GuoWang.WZ
noncomputable section
variable {K : Type*} [Field K]

lemma ft_shift_A (q a : K) (e k : ℕ) (hd : pd q a k ≠ 0) (hq : q ≠ 0) (ha : a ≠ 0)
    (h₁ : 1-a*q ≠ 0) (h₃ : 1-a*q^3 ≠ 0) (h₄ : 1-a*q^4 ≠ 0)
    (hx₁ : a*q-q^(2*k) ≠ 0) (hx₃ : a*q^3-q^(2*k) ≠ 0)
    (ht : 1-q^(4*k)/a ≠ 0) (hu : 1-a⁻¹ ≠ 0)
    (hv : 1-a*q^4*(q^(2*k))^2 ≠ 0) :
    ft q (a*q^4) 2 6 e k = shiftA q a (q^(2*k)) * ft q a 2 6 e k := by
  unfold ft
  rw [pair_shift_two q a k hq ha h₁ h₃ hx₁ hx₃, pd_shift q a k hq ha h₄ ht]
  have he : q^(4*k) = (q^(2*k))^2 := by rw [← pow_mul]; congr 1; omega
  rw [he] at *
  have hs : a-1 ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    simp [he'] at hu
  unfold shiftA
  field_simp [hd, hs, ha, hq, h₁, h₃, h₄, hx₁, hx₃, ht, hu, hv]

#print axioms ft_shift_A
end
end GuoWang.WZ
```

### `GWFieldShiftB.lean`

```lean
import GWFieldTerms

namespace GuoWang.WZ
noncomputable section
variable {K : Type*} [Field K]

lemma ft_shift_B (q a : K) (e k : ℕ) (hd : pd q a k ≠ 0) (hq : q ≠ 0) (ha : a ≠ 0)
    (h₁ : 1-a*q ≠ 0) (h₄ : 1-a*q^4 ≠ 0)
    (hx₃ : a*q^3-q^(4*k) ≠ 0) (ht : 1-q^(4*k)/a ≠ 0)
    (hu : 1-a⁻¹ ≠ 0) (hv : 1-a*q^4*q^(4*k) ≠ 0) :
    ft q (a*q^4) 4 8 e k = shiftB q a (q^(4*k)) * ft q a 4 8 e k := by
  unfold ft
  rw [pair_shift_four q a k hq ha h₁ hx₃, pd_shift q a k hq ha h₄ ht]
  have hs : a-1 ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    simp [he'] at hu
  unfold shiftB
  field_simp [hd, hs, ha, hq, h₁, h₄, hx₃, ht, hu, hv]

#print axioms ft_shift_B
end
end GuoWang.WZ
```

### `GWFieldLegal.lean`

```lean
import GWFieldShiftA
import GWFieldShiftB

/-! Generic legality, with a genuinely independent parameter intended at use.
These are local certificate conditions, never endpoint hypotheses. -/
namespace GuoWang.WZ
open QWZCore
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

structure Good (q a : K) : Prop where
  q_ne : q ≠ 0
  a_ne : a ≠ 0
  pow_ne : ∀ m : ℕ, 0 < m → 1-q^m ≠ 0
  param_ne : ∀ i j : ℕ, a*q^i-q^j ≠ 0

namespace Good
variable {q a : K} (h : Good q a)
include h

lemma one_sub (m : ℕ) : 1-a*q^m ≠ 0 := by
  exact sub_ne_zero.mpr (sub_ne_zero.mp (by simpa only [pow_zero] using h.param_ne m 0)).symm

lemma one_div (m : ℕ) : 1-q^m/a ≠ 0 := by
  have he : 1-q^m/a = (a-q^m)/a := by field_simp [h.a_ne]
  rw [he]
  exact div_ne_zero (by simpa using h.param_ne 0 m) h.a_ne

lemma inv_sub : 1-a⁻¹ ≠ 0 := by simpa using h.one_div 0

lemma shift : Good q (a*q^4) where
  q_ne := h.q_ne
  a_ne := mul_ne_zero h.a_ne (pow_ne_zero 4 h.q_ne)
  pow_ne := h.pow_ne
  param_ne i j := by
    have he : a*q^4*q^i = a*q^(4+i) := by rw [pow_add]; ring
    rw [he]
    exact h.param_ne _ _

lemma pd_ne (k : ℕ) : pd q a k ≠ 0 := by
  unfold pd pair QWZCore.poch
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro j _
      rw [← pow_mul, show a*q^4*q^(4*j) = a*q^(4+4*j) by rw [pow_add]; ring]
      exact h.one_sub _
    · apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have he : q^4/a*(q^4)^j = q^(4+4*j)/a := by rw [← pow_mul, pow_add]; ring
      rw [he]
      exact h.one_div _
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [← pow_mul, ← pow_add]
    exact h.pow_ne _ (by omega)

lemma den_ne (k : ℕ) : (GuoWang.Clear.den q k).eval a ≠ 0 := by
  rw [GuoWang.Clear.den, GuoWang.Clear.eval_pairPoch_field q a 4 4 k h.a_ne]
  exact mul_ne_zero (pow_ne_zero k h.a_ne) (h.pd_ne k)

lemma qInt_eq (m : ℕ) : (∑ j ∈ Finset.range m, q^j) = (1-q^m)/(1-q) := by
  apply (eq_div_iff (by simpa using h.pow_ne 1 (by omega))).mpr
  have he := geom_sum_mul q m
  linear_combination -he

lemma qInt_ne (m : ℕ) (hm : 0 < m) : (∑ j ∈ Finset.range m, q^j) ≠ 0 := by
  rw [h.qInt_eq]
  exact div_ne_zero (h.pow_ne m hm) (by simpa using h.pow_ne 1 (by omega))

lemma qInt_ratio (m r : ℕ) :
    (∑ j ∈ Finset.range m, q^j)/(∑ j ∈ Finset.range r, q^j) = (1-q^m)/(1-q^r) := by
  rw [h.qInt_eq, h.qInt_eq]
  exact div_div_div_cancel_right₀ (by simpa using h.pow_ne 1 (by omega)) _ _

end Good
#print axioms Good.pd_ne
#print axioms Good.shift
end
end GuoWang.WZ
```

### `GWFieldNext.lean`

```lean
import GWFieldLegal

/-! Generic successor ratios for the two literal finite-product models. -/
namespace GuoWang.WZ
open Polynomial
open scoped BigOperators
open GuoWang.Clear
noncomputable section
variable {K : Type*} [Field K]

lemma eval_factor (q a : K) (t s k : ℕ) (ha : a ≠ 0) :
    (factor q t s k).eval a =
      a*((1-a*q^(t+s*k))*(1-q^(t+s*k)/a)*(1-q^(t+s*k))) := by
  simp only [GuoWang.Clear.factor, eval_mul, eval_sub, eval_one, eval_X, eval_C]
  field_simp

lemma factor_quotient (q a : K) (s k : ℕ) (ha : a ≠ 0) :
    (factor q 1 s k).eval a / (factor q 4 4 k).eval a =
      ((1-a*q^(1+s*k))*(1-q^(1+s*k)/a)*(1-q^(1+s*k))) /
        ((1-a*q^(4+4*k))*(1-q^(4+4*k)/a)*(1-q^(4+4*k))) := by
  rw [eval_factor _ _ _ _ _ ha, eval_factor _ _ _ _ _ ha]
  exact mul_div_mul_left _ _ ha

lemma ft_next_A (q a : K) (h : Good q a) (k : ℕ) :
    ft q a 2 6 (3*(k+1)^2) (k+1) = nextA q a (q^(2*k)) * ft q a 2 6 (3*k^2) k := by
  simp only [ft_eq_term q a _ _ _ _ h.a_ne]
  have ht := term_succ q a 2 6 (3*k^2) (6*k+3) k (h.qInt_ne _ (by omega))
    (h.den_ne k) (factor_den_ne_zero q a k (h.den_ne (k+1)))
  rw [show 3*k^2+(6*k+3) = 3*(k+1)^2 by ring] at ht
  rw [ht]
  congr 1
  calc
    _ = -((∑ j ∈ Finset.range (6*(k+1)+1), q^j)/(∑ j ∈ Finset.range (6*k+1), q^j))*q^(6*k+3) *
        ((factor q 1 2 k).eval a / (factor q 4 4 k).eval a) := by ring
    _ = _ := by
      rw [h.qInt_ratio, factor_quotient _ _ _ _ h.a_ne]
      have e₁ : q^(6*(k+1)+1) = q^7*(q^(2*k))^3 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e₂ : q^(6*k+1) = q*(q^(2*k))^3 := by
        rw [← pow_mul, ← pow_succ']; congr 1; omega
      have e₃ : q^(6*k+3) = q^3*(q^(2*k))^3 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e₄ : q^(1+2*k) = q*q^(2*k) := by rw [pow_add, pow_one]
      have e₅ : q^(4+4*k) = q^4*(q^(2*k))^2 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      rw [e₁, e₂, e₃, e₄, e₅]
      unfold nextA
      ring

lemma ft_next_B (q a : K) (h : Good q a) (k : ℕ) :
    ft q a 4 8 (2*(k+1)^2+(k+1)) (k+1) =
      nextB q a (q^(4*k)) * ft q a 4 8 (2*k^2+k) k := by
  simp only [ft_eq_term q a _ _ _ _ h.a_ne]
  have ht := term_succ q a 4 8 (2*k^2+k) (4*k+3) k (h.qInt_ne _ (by omega))
    (h.den_ne k) (factor_den_ne_zero q a k (h.den_ne (k+1)))
  rw [show 2*k^2+k+(4*k+3) = 2*(k+1)^2+(k+1) by ring] at ht
  rw [ht]
  congr 1
  calc
    _ = -((∑ j ∈ Finset.range (8*(k+1)+1), q^j)/(∑ j ∈ Finset.range (8*k+1), q^j))*q^(4*k+3) *
        ((factor q 1 4 k).eval a / (factor q 4 4 k).eval a) := by ring
    _ = _ := by
      rw [h.qInt_ratio, factor_quotient _ _ _ _ h.a_ne]
      have e₁ : q^(8*(k+1)+1) = q^9*(q^(4*k))^2 := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have e₂ : q^(8*k+1) = q*(q^(4*k))^2 := by
        rw [← pow_mul, ← pow_succ']; congr 1; omega
      have e₃ : q^(4*k+3) = q^3*q^(4*k) := by rw [← pow_add]; congr 1; omega
      have e₄ : q^(1+4*k) = q*q^(4*k) := by rw [pow_add, pow_one]
      rw [e₁, e₂, e₃, e₄, pow_add q 4 (4*k)]
      unfold nextB
      ring

#print axioms ft_next_A
#print axioms ft_next_B
end
end GuoWang.WZ
```

### `GWFieldRecurrence.lean`

```lean
import GWFieldNext
import GWTelescope

/-! Full finite WZ recurrence for actual field-valued summands. -/
namespace GuoWang.WZ
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

def fa (q a : K) (k : ℕ) : K := ft q a 2 6 (3*k^2) k
def fb (q a : K) (k : ℕ) : K := ft q a 4 8 (2*k^2+k) k
def fd (q a : K) (N : ℕ) : K :=
  (∑ k ∈ Finset.range N, fa q a k) - ∑ k ∈ Finset.range N, fb q a k

def ga (q a : K) (k : ℕ) : K := fa q a k * gA q a (q^(2*k))
def gb (q a : K) (k : ℕ) : K := fb q a k * gB q a (q^(4*k))

lemma Good.qfactor {q a : K} (h : Good q a) (r s t : ℕ) (hr : 0 < r) :
    1-q^r*(q^s)^t ≠ 0 := by
  rw [← pow_mul, ← pow_add]
  exact h.pow_ne _ (by omega)

lemma Good.afactor {q a : K} (h : Good q a) (r s t : ℕ) :
    1-a*q^r*(q^s)^t ≠ 0 := by
  rw [← pow_mul, mul_assoc, ← pow_add]
  exact h.one_sub _

lemma Good.divfactor {q a : K} (h : Good q a) (r s t : ℕ) :
    1-q^r*(q^s)^t/a ≠ 0 := by
  rw [← pow_mul, ← pow_add]
  exact h.one_div _

lemma Good.diffactor {q a : K} (h : Good q a) (i r s : ℕ) :
    a*q^i-q^r*q^s ≠ 0 := by
  rw [← pow_add]
  exact h.param_ne _ _

lemma fa_step (q a : K) (h : Good q a) (k : ℕ) :
    (1-a⁻¹)*fa q (a*q^4) k-(1-a*q^4)*fa q a k = ga q a (k+1)-ga q a k := by
  have hc := rational_certificate_A q a (q^(2*k)) h.a_ne h.inv_sub
    (by simpa using h.qfactor 1 (2*k) 3 (by omega))
    (by simpa using h.param_ne 1 (2*k)) (h.afactor 4 (2*k) 2)
    (h.param_ne 3 (2*k)) (h.divfactor 4 (2*k) 2)
    (h.qfactor 4 (2*k) 2 (by omega)) (h.qfactor 7 (2*k) 3 (by omega))
    (h.diffactor 3 2 (2*k)) (by simpa using h.diffactor 1 2 (2*k))
  unfold ga fa
  rw [ft_shift_A q a (3*k^2) k (h.pd_ne k) h.q_ne h.a_ne (by simpa using h.one_sub 1) (h.one_sub 3)
    (h.one_sub 4) (by simpa using h.param_ne 1 (2*k)) (h.param_ne 3 (2*k))
    (h.one_div (4*k)) h.inv_sub (h.afactor 4 (2*k) 2), ft_next_A q a h k]
  have he : q^(2*(k+1)) = q^2*q^(2*k) := by rw [← pow_add]; congr 1; omega
  rw [he]
  linear_combination (ft q a 2 6 (3*k^2) k) * hc

lemma fb_step (q a : K) (h : Good q a) (k : ℕ) :
    (1-a⁻¹)*fb q (a*q^4) k-(1-a*q^4)*fb q a k = gb q a (k+1)-gb q a k := by
  have hc := rational_certificate_B q a (q^(4*k)) h.a_ne h.inv_sub
    (by simpa using h.qfactor 1 (4*k) 2 (by omega))
    (by simpa using h.one_sub 1) (by simpa using h.afactor 4 (4*k) 1)
    (h.param_ne 3 (4*k)) (by simpa using h.divfactor 4 (4*k) 1)
    (by simpa using h.qfactor 4 (4*k) 1 (by omega))
    (h.qfactor 9 (4*k) 2 (by omega)) (h.diffactor 3 4 (4*k))
  unfold gb fb
  rw [ft_shift_B q a (2*k^2+k) k (h.pd_ne k) h.q_ne h.a_ne (by simpa using h.one_sub 1)
    (h.one_sub 4) (h.param_ne 3 (4*k)) (h.one_div (4*k))
    h.inv_sub (by simpa using h.afactor 4 (4*k) 1), ft_next_B q a h k]
  have he : q^(4*(k+1)) = q^4*q^(4*k) := by rw [← pow_add]; congr 1; omega
  rw [he]
  linear_combination (ft q a 4 8 (2*k^2+k) k) * hc

@[simp] lemma ga_zero (q a : K) : ga q a 0 = 0 := by simp [ga, gA]
@[simp] lemma gb_zero (q a : K) : gb q a 0 = 0 := by simp [gb, gB]

/-- The common recurrence is proved once for all legal generic field inputs;
the parameter may itself be an independent rational-function variable. -/
theorem fd_recurrence (q a : K) (h : Good q a) (N : ℕ) :
    (1-a⁻¹)*fd q (a*q^4) N-(1-a*q^4)*fd q a N = ga q a N-gb q a N := by
  exact finite_difference_recurrence _ _ _ _ _ _ _ _ N
    (fun k _ => fa_step q a h k) (fun k _ => fb_step q a h k)
    (ga_zero q a) (gb_zero q a)

#print axioms fa_step
#print axioms fb_step
#print axioms fd_recurrence
end
end GuoWang.WZ
```

### `GWBoundaryAlgebra.lean`

```lean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Isolate the boundary cancellation from all finite-product syntax. -/
namespace GuoWang.WZ
variable {K : Type*} [Field K]

lemma cancel_boundary (w h q num d t u v r c : K)
    (hq : 1-q ≠ 0) (hh : h ≠ 0) (hd : d ≠ 0) (ht : t ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) (hr : r ≠ 0) :
    (w*(h/(1-q))*num/(d*t*u))*(c*t*u/(h*v*r)) =
      w*c*num/((1-q)*d*v*r) := by
  field_simp [hq, hh, hd, ht, hu, hv, hr]

end GuoWang.WZ
```

### `GWBoundaryTerms.lean`

```lean
import GWFieldRecurrence

/-! Cancelled boundaries before any terminating-parameter specialization. -/
namespace GuoWang.WZ
open QWZCore
noncomputable section
variable {K : Type*} [Field K]

def boundaryDen (q a : K) (N : ℕ) : K :=
  (1-q)*QWZCore.poch (a*q^4) (q^4) N *
    QWZCore.poch (q^4/a) (q^4) (N-1)*QWZCore.poch (q^4) (q^4) (N-1)

def ca (q a : K) (N : ℕ) : K :=
  (-1)^(N+1)*c q a*q^(3*N^2)*
    (pair q a 1 2 N*QWZCore.poch q (q^2) N) /
    (boundaryDen q a N*(a*q^3-q^(2*N))*(a*q-q^(2*N)))

def cb (q a : K) (N : ℕ) : K :=
  (-1)^N*c q a*q^(2*N^2+N)*
    (pair q a 1 4 N*QWZCore.poch q (q^4) N) /
    (boundaryDen q a N*(a*q^3-q^(4*N))*(1-a*q))

end
end GuoWang.WZ
```

### `GWBoundaryA.lean`

```lean
import GWBoundaryTerms
import GWBoundaryAlgebra

namespace GuoWang.WZ
noncomputable section
variable {K : Type*} [Field K]

lemma ga_cancelled (q a : K) (h : Good q a) (N : ℕ) (hN : 0 < N) :
    ga q a N = ca q a N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have he₁ : (∑ j ∈ Finset.range (6*(k+1)+1), q^j) =
      (1-q*(q^(2*(k+1)))^3)/(1-q) := by
    rw [h.qInt_eq]
    congr 2
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  have he₂ : q^4*(q^4)^k = (q^(2*(k+1)))^2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
  have hfull := h.pd_ne (k+1)
  have htail := h.pd_ne k
  change (_ * _ * _) ≠ 0 at hfull htail
  have hfa := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hfull).1).1
  have htb := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htail).1).2
  have htc := (mul_ne_zero_iff.mp htail).2
  unfold ga fa ft pd pair ca boundaryDen gA
  rw [he₁]
  simp only [Nat.succ_sub_one, pair, pow_one, QWZCore.poch_succ (q^4/a) (q^4) k,
    QWZCore.poch_succ (q^4) (q^4) k, div_mul_eq_mul_div, he₂, pow_succ (-1:K)]
  have hq : 1-q ≠ 0 := by simpa using h.pow_ne 1 (by omega)
  have hx : 1-q*(q^(2*(k+1)))^3 ≠ 0 := by simpa using h.qfactor 1 (2*(k+1)) 3 (by omega)
  have ht : 1-(q^(2*(k+1)))^2/a ≠ 0 := by
    simpa only [← pow_mul, show 2*(k+1)*2 = 4*(k+1) by omega] using h.one_div (4*(k+1))
  have hu : 1-(q^(2*(k+1)))^2 ≠ 0 := by
    rw [← pow_mul]; exact h.pow_ne _ (by omega)
  have hv := h.param_ne 3 (2*(k+1))
  have hr : a*q-q^(2*(k+1)) ≠ 0 := by simpa using h.param_ne 1 (2*(k+1))
  have hc' := cancel_boundary
    ((-1)^(k+1)*q^(3*(k+1)^2)) (1-q*(q^(2*(k+1)))^3) q
    (pair q a 1 2 (k+1)*QWZCore.poch q (q^2) (k+1))
    (QWZCore.poch (a*q^4) (q^4) (k+1)*QWZCore.poch (q^4/a) (q^4) k*
      QWZCore.poch (q^4) (q^4) k)
    (1-(q^(2*(k+1)))^2/a) (1-(q^(2*(k+1)))^2)
    (a*q^3-q^(2*(k+1))) (a*q-q^(2*(k+1))) (-c q a)
    hq hx (mul_ne_zero (mul_ne_zero hfa htb) htc) ht hu hv hr
  simp only [pair, pow_one, pow_succ (-1:K)] at hc'
  simp only [Nat.succ_eq_add_one] at *
  convert hc' using 1 <;> ring

#print axioms ga_cancelled
end
end GuoWang.WZ
```

### `GWBoundaryB.lean`

```lean
import GWBoundaryTerms
import GWBoundaryAlgebra

namespace GuoWang.WZ
noncomputable section
variable {K : Type*} [Field K]

lemma gb_cancelled (q a : K) (h : Good q a) (N : ℕ) (hN : 0 < N) :
    gb q a N = cb q a N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have he₁ : (∑ j ∈ Finset.range (8*(k+1)+1), q^j) =
      (1-q*(q^(4*(k+1)))^2)/(1-q) := by
    rw [h.qInt_eq]
    congr 2
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  have he₂ : q^4*(q^4)^k = q^(4*(k+1)) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hfull := h.pd_ne (k+1)
  have htail := h.pd_ne k
  change (_ * _ * _) ≠ 0 at hfull htail
  have hfa := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hfull).1).1
  have htb := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htail).1).2
  have htc := (mul_ne_zero_iff.mp htail).2
  unfold gb fb ft pd pair cb boundaryDen gB
  rw [he₁]
  simp only [Nat.succ_sub_one, pair, pow_one, QWZCore.poch_succ (q^4/a) (q^4) k,
    QWZCore.poch_succ (q^4) (q^4) k, div_mul_eq_mul_div, he₂]
  have hq : 1-q ≠ 0 := by simpa using h.pow_ne 1 (by omega)
  have hx : 1-q*(q^(4*(k+1)))^2 ≠ 0 := by simpa using h.qfactor 1 (4*(k+1)) 2 (by omega)
  have ht := h.one_div (4*(k+1))
  have hu := h.pow_ne (4*(k+1)) (by omega)
  have hv := h.param_ne 3 (4*(k+1))
  have hr : 1-a*q ≠ 0 := by simpa using h.one_sub 1
  have hc' := cancel_boundary
    ((-1)^(k+1)*q^(2*(k+1)^2+(k+1))) (1-q*(q^(4*(k+1)))^2) q
    (pair q a 1 4 (k+1)*QWZCore.poch q (q^4) (k+1))
    (QWZCore.poch (a*q^4) (q^4) (k+1)*QWZCore.poch (q^4/a) (q^4) k*
      QWZCore.poch (q^4) (q^4) k)
    (1-q^(4*(k+1))/a) (1-q^(4*(k+1)))
    (a*q^3-q^(4*(k+1))) (1-a*q) (c q a)
    hq hx (mul_ne_zero (mul_ne_zero hfa htb) htc) ht hu hv hr
  simp only [pair, pow_one] at hc'
  simp only [Nat.succ_eq_add_one] at *
  convert hc' using 1 <;> ring

#print axioms gb_cancelled
end
end GuoWang.WZ
```

### `GWCancelledBoundary.lean`

```lean
import GWBoundaryA
import GWBoundaryB

namespace GuoWang.WZ
noncomputable section
variable {K : Type*} [Field K]

theorem fd_cancelled_recurrence (q a : K) (h : Good q a) (N : ℕ) (hN : 0 < N) :
    (1-a⁻¹)*fd q (a*q^4) N-(1-a*q^4)*fd q a N = ca q a N-cb q a N := by
  rw [fd_recurrence q a h, ga_cancelled q a h N hN, gb_cancelled q a h N hN]

#print axioms fd_cancelled_recurrence
end
end GuoWang.WZ
```

### `GWIndependent.lean`

```lean
import GWFieldRecurrence

/-! The generic field model uses an actual independent parameter. -/
namespace GuoWang.WZ
open Polynomial
noncomputable section

abbrev F := RatFunc ℚ
abbrev E := RatFunc F

def genericQ : E := algebraMap F E GuoWang.X'
def genericA : E := RatFunc.X

lemma linear_generic_ne (c d : F) (hc : c ≠ 0) :
    genericA*algebraMap F E c-algebraMap F E d ≠ 0 := by
  have hp : (X*C c-C d : F[X]) ≠ 0 := by
    intro he
    have he' := congrArg (fun f : F[X] => f.coeff 1) he
    simp only [coeff_sub, coeff_X_mul, coeff_C, ite_eq_right (by decide : (1:ℕ) ≠ 0), sub_zero] at he'
    exact hc he'
  have he : algebraMap F[X] E (X*C c-C d) = genericA*algebraMap F E c-algebraMap F E d := by
    simp only [map_sub, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    rfl
  rw [← he]
  exact RatFunc.algebraMap_ne_zero hp

/-- None of the generic certificate hypotheses is a vacuous assumption. -/
theorem generic_good : Good genericQ genericA where
  q_ne := (_root_.map_ne_zero (algebraMap F E)).mpr GuoWang.X'_ne_zero
  a_ne := RatFunc.X_ne_zero
  pow_ne m hm := by
    have he : 1-genericQ^m = algebraMap F E (1-GuoWang.X'^m) := by simp [genericQ]
    rw [he]
    exact (_root_.map_ne_zero (algebraMap F E)).mpr (GuoWang.one_sub_X'_pow_ne_zero m hm)
  param_ne i j := by
    simpa only [genericQ, ← map_pow] using
      linear_generic_ne (GuoWang.X'^i) (GuoWang.X'^j) (pow_ne_zero i GuoWang.X'_ne_zero)

lemma fa_scalar (q a : F) (k : ℕ) : fa q a k = GuoWang.A q a k := by
  unfold fa ft pd pair GuoWang.A GuoWang.paramDen
  simp only [GuoWang.poch_eq_core, pow_one]

lemma fb_scalar (q a : F) (k : ℕ) : fb q a k = GuoWang.B q a k := by
  unfold fb ft pd pair GuoWang.B GuoWang.paramDen
  simp only [GuoWang.poch_eq_core, pow_one]

lemma fd_scalar (q a : F) (N : ℕ) : fd q a N = GuoWang.D N q a := by
  simp only [fd, GuoWang.D, fa_scalar, fb_scalar]

/-- Exact finite-sum fidelity for all generic legal field inputs. -/
lemma fd_fraction {K : Type*} [Field K] (q a : K) (h : Good q a) (N : ℕ) :
    fd q a N = (GuoWang.Clear.commonNum q N).eval a / (GuoWang.Clear.commonDen q N).eval a := by
  rw [GuoWang.Clear.common_fraction q a N (fun k _ => h.den_ne k)]
  simp only [fd, fa, fb, ft_eq_term q a _ _ _ _ h.a_ne, GuoWang.Clear.term]

/-- A true independent-parameter recurrence, not a recurrence conditional on
unproved ratio identities. -/
theorem generic_recurrence (N : ℕ) :
    (1-genericA⁻¹)*fd genericQ (genericA*genericQ^4) N-
      (1-genericA*genericQ^4)*fd genericQ genericA N = ga genericQ genericA N-gb genericQ genericA N :=
  fd_recurrence _ _ generic_good N

#print axioms generic_good
#print axioms fd_fraction
#print axioms generic_recurrence
end
end GuoWang.WZ
```

### `GWInverseRoot.lean`

```lean
import GWClearSpecialize
import GWClearRoots
import Mathlib.Algebra.Polynomial.Degree.Support

/-! Transfer an inverse-parameter root to a root of the ordinary polynomial
at a=1. This avoids adjoining arbitrary rational-function units. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section

/-- Clear only powers of q from the inverse substitution. -/
def inverseNumerator (f : Polynomial ℚ[X]) (n : ℕ) : ℚ[X] :=
  ∑ i ∈ f.support, f.coeff i * (X^n)^(f.natDegree-i)

lemma inverseNumerator_map (f : Polynomial ℚ[X]) (n : ℕ) :
    qMap (inverseNumerator f n) =
      (GuoWang.X'^n)^f.natDegree * spec (GuoWang.X'^n)⁻¹ f := by
  simp only [inverseNumerator, map_sum, map_mul, map_pow, RatFunc.algebraMap_X]
  change _ = (GuoWang.X'^n)^f.natDegree * eval₂ qMap (GuoWang.X'^n)⁻¹ f
  rw [eval₂_eq_sum, sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle := le_natDegree_of_mem_supp i hi
  have hz := pow_ne_zero n GuoWang.X'_ne_zero
  have he : (GuoWang.X'^n)^f.natDegree * ((GuoWang.X'^n)⁻¹)^i =
      (GuoWang.X'^n)^(f.natDegree-i) := by
    simpa only [inv_pow] using (pow_sub₀ (GuoWang.X'^n) hz hle).symm
  rw [mul_left_comm, he]
  rfl

lemma inverseNumerator_at_root {K : Type*} [Field K] [CharZero K]
    (f : Polynomial ℚ[X]) (n : ℕ) (z : K) (hz : z^n = 1) :
    aeval z (inverseNumerator f n) = aeval z (f.eval 1) := by
  simp only [inverseNumerator, map_sum, map_mul, map_pow, aeval_X, hz, one_pow, mul_one]
  rw [eval_eq_sum, sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- This root transfer keeps the cyclotomic factor in ℚ[q], where it is not a
unit. Only the q-monomial in inverseNumerator_map was cleared. -/
theorem inverse_root_specializes {K : Type*} [Field K] [CharZero K]
    (f : Polynomial ℚ[X]) (n : ℕ) (z : K) (hz : z^n = 1)
    (hf : spec (GuoWang.X'^n)⁻¹ f = 0) : aeval z (f.eval 1) = 0 := by
  have hm : inverseNumerator f n = 0 := by
    apply RatFunc.algebraMap_injective ℚ
    rw [inverseNumerator_map, hf, mul_zero, map_zero]
  rw [← inverseNumerator_at_root f n z hz, hm, map_zero]

#print axioms inverseNumerator_map
#print axioms inverse_root_specializes
end
end GuoWang.Clear
```

### `GWExtractFourth.lean`

```lean
import GWInverseRoot
import GWClearTop
import QSpecialize

/-! The fourth-power extraction stays entirely over ℚ[q]. The inverse root
is handled by clearing q-monomials, so cyclotomic factors cannot become units. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section

lemma spec_positive (f : Polynomial ℚ[X]) (n : ℕ) :
    spec (GuoWang.X'^n) f = qMap (f.eval ((X : ℚ[X])^n)) := by
  simpa only [spec, coe_eval₂RingHom, map_pow, RatFunc.algebraMap_X, GuoWang.X'] using
    (eval₂_at_apply (p := f) qMap ((X : ℚ[X])^n))

lemma positive_ne_inverse (n : ℕ) (hn : 0 < n) :
    GuoWang.X'^n ≠ (GuoWang.X'^n)⁻¹ := by
  intro he
  apply GuoWang.X'_pow_ne_one (n+n) (by omega)
  rw [pow_add]
  nth_rw 1 [he]
  exact inv_mul_cancel₀ (pow_ne_zero n GuoWang.X'_ne_zero)

/-- Coefficientwise Φ_n² and the two genuine parameter zeros imply Φ_n⁴ at
1. The hypotheses are the remaining mathematical inputs, not extra hypotheses
of a claimed universal endpoint. -/
theorem fourth_of_parameter_roots {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : 0 < n) (z : K) (hz : IsPrimitiveRoot z n)
    (hc : C ((cyclotomic n ℚ)^2) ∣ P n)
    (hp : spec (GuoWang.X'^n) (P n) = 0)
    (hm : spec (GuoWang.X'^n)⁻¹ (P n) = 0) :
    (cyclotomic n ℚ)^4 ∣ Pone n := by
  let c : ℚ[X] := (cyclotomic n ℚ)^2
  have hcn : c ≠ 0 := pow_ne_zero 2 (cyclotomic.monic n ℚ).ne_zero
  have hcmap : qMap c ≠ 0 := RatFunc.algebraMap_ne_zero hcn
  obtain ⟨f, hf⟩ := hc
  have hp' : spec (GuoWang.X'^n) f = 0 := by
    rw [hf, map_mul] at hp
    simp only [spec, coe_eval₂RingHom, eval₂_C] at hp
    change qMap c * spec (GuoWang.X'^n) f = 0 at hp
    exact (mul_eq_zero.mp hp).resolve_left hcmap
  have hm' : spec (GuoWang.X'^n)⁻¹ f = 0 := by
    rw [hf, map_mul] at hm
    simp only [spec, coe_eval₂RingHom, eval₂_C] at hm
    change qMap c * spec (GuoWang.X'^n)⁻¹ f = 0 at hm
    exact (mul_eq_zero.mp hm).resolve_left hcmap
  have hp_eval : f.eval ((X : ℚ[X])^n) = 0 := by
    apply RatFunc.algebraMap_injective ℚ
    rw [← spec_positive, hp', map_zero]
  obtain ⟨g, hg⟩ := (dvd_iff_isRoot.mpr hp_eval : X-C ((X : ℚ[X])^n) ∣ f)
  have hmg : spec (GuoWang.X'^n)⁻¹ g = 0 := by
    rw [hg, map_mul] at hm'
    have he : spec (GuoWang.X'^n)⁻¹ (X-C ((X : ℚ[X])^n)) =
        (GuoWang.X'^n)⁻¹-GuoWang.X'^n := by simp [spec, GuoWang.X']
    rw [he] at hm'
    exact (mul_eq_zero.mp hm').resolve_left
      (sub_ne_zero.mpr (positive_ne_inverse n hn).symm)
  have hgroot : aeval z (g.eval 1) = 0 :=
    inverse_root_specializes g n z hz.pow_eq_one hmg
  obtain ⟨u, hu⟩ := (cyclotomic_dvd_iff_root hn hz (g.eval 1)).mpr hgroot
  have hzpoly : cyclotomic n ℚ ∣ (1-(X : ℚ[X])^n) := by
    apply (cyclotomic_dvd_iff_root hn hz _).mpr
    simp [hz.pow_eq_one]
  obtain ⟨v, hv⟩ := hzpoly
  refine ⟨v*u, ?_⟩
  unfold Pone
  rw [hf, hg]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  rw [hu, hv]
  change (cyclotomic n ℚ)^2 * ((cyclotomic n ℚ*v) * (cyclotomic n ℚ*u)) = _
  ring

/-- The previous bridge applies to the exact reduced numerator, with top
specialization denominators already proved coprime and nonzero. -/
theorem top_fourth_of_parameter_roots {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) (z : K) (hz : IsPrimitiveRoot z n)
    (hc : C ((cyclotomic n ℚ)^2) ∣ P n)
    (hp : spec (GuoWang.X'^n) (P n) = 0)
    (hm : spec (GuoWang.X'^n)⁻¹ (P n) = 0) :
    (cyclotomic n ℚ)^4 ∣ (GuoWang.diff n).num := by
  apply (top_reduced_num_iff n h4 4).mpr
  exact fourth_of_parameter_roots n hn z hz hc hp hm

#print axioms fourth_of_parameter_roots
#print axioms top_fourth_of_parameter_roots
end
end GuoWang.Clear
```

### `GWResidueProducts.lean`

```lean
import QCyclic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination

/-! Complete and deleted residue products. The deleted product is recovered
by differentiating a single complete product, avoiding explicit permutations. -/
namespace GuoWang.Residues
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma complete_product {z : K} {n : ℕ} (hz : IsPrimitiveRoot z n) (hn : 0 < n)
    (s : ℕ) (hs : n.Coprime s) (a : K) :
    (∏ j ∈ Finset.range n, (1-a*z^(1+s*j))) = 1-a^n := by
  have hp := QWZCore.prod_one_sub_mul_pow (hz.pow_of_coprime s hs.symm) hn (a*z)
  have he : (a*z)^n = a^n := by rw [mul_pow, hz.pow_eq_one, mul_one]
  rw [he] at hp
  convert hp using 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add, pow_one, pow_mul]
  ring

/-- Polynomial form of the entire residue-cycle product. -/
lemma complete_polynomial {z : K} {n : ℕ} (hz : IsPrimitiveRoot z n) (hn : 0 < n)
    (s : ℕ) (hs : n.Coprime s) :
    (∏ j ∈ Finset.range n, (1-X*C (z^(1+s*j)) : K[X])) = 1-X^n := by
  apply Polynomial.funext
  intro a
  simpa only [eval_prod, eval_sub, eval_one, eval_mul, eval_X, eval_C, eval_pow] using
    complete_product hz hn s hs a

/-- Deleting any factor whose residue is zero leaves the same product n.
No choice of a residue permutation, or division by a zero factor, is used. -/
theorem deleted_product {z : K} {n : ℕ} (hz : IsPrimitiveRoot z n) (hn : 0 < n)
    (s : ℕ) (hs : n.Coprime s) (j₀ : ℕ) (hj : j₀ < n)
    (hzero : z^(1+s*j₀) = 1) :
    (∏ j ∈ (Finset.range n).erase j₀, (1-z^(1+s*j))) = (n : K) := by
  let p : K[X] := ∏ j ∈ (Finset.range n).erase j₀, (1-X*C (z^(1+s*j)))
  have he : (1-X)*p = (1-X^n : K[X]) := by
    have hprod := Finset.mul_prod_erase (Finset.range n)
      (fun j => (1-X*C (z^(1+s*j)) : K[X])) (Finset.mem_range.mpr hj)
    simpa only [hzero, C_1, mul_one, complete_polynomial hz hn s hs] using hprod
  have hd := congrArg (fun f : K[X] => f.derivative.eval 1) he
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_X,
    derivative_X_pow, eval_add, eval_mul, eval_sub, eval_zero, eval_one,
    eval_C, eval_X, eval_pow, one_pow, sub_self, zero_mul, add_zero] at hd
  have hp : p.eval 1 = (n : K) := by linear_combination -hd
  simpa only [p, eval_prod, eval_sub, eval_one, eval_mul, eval_X, eval_C, one_mul] using hp

#print axioms complete_product
#print axioms deleted_product
end
end GuoWang.Residues
```

### `GWShiftObstruction.lean`

```lean
import GWClearShift
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! A shorter alternative to orbit multiplication: the homogeneous parameter
shift has no nonzero rational solution, by order at a=0. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

lemma coeff_rescale (u : K) (p : K[X]) (i : ℕ) :
    (rescale u p).coeff i = p.coeff i*u^i := by
  simp only [rescale_apply, mul_comm (X : K[X]) (C u), comp_C_mul_X_coeff]

lemma trailing_rescale (u : K) (hu : u ≠ 0) (p : K[X]) :
    (rescale u p).natTrailingDegree = p.natTrailingDegree := by
  have hs : (rescale u p).support = p.support := by
    ext i
    rw [mem_support_iff, mem_support_iff, coeff_rescale, mul_ne_zero_iff]
    exact and_iff_left (pow_ne_zero i hu)
  simp only [natTrailingDegree, trailingDegree, hs]

/-- No rational p/h can satisfy the homogeneous parameter equation. -/
theorem homogeneous_shift_zero (u : K) (hu : u ≠ 0) (p h : K[X]) (hh : h ≠ 0)
    (he : (X-1)*rescale u p*h = X*(1-X*C u)*p*rescale u h) : p = 0 := by
  by_contra hp
  have hsp := rescale_ne_zero u hu p hp
  have hsh := rescale_ne_zero u hu h hh
  have hx : (X-1 : K[X]) ≠ 0 := (monic_X_sub_C 1).ne_zero
  have hy : (1-X*C u : K[X]) ≠ 0 := by
    intro heq
    have hc := congrArg (fun f : K[X] => f.coeff 0) heq
    simp at hc
  have tx : (X-1 : K[X]).natTrailingDegree = 0 := by
    apply natTrailingDegree_eq_zero.mpr
    right
    simp
  have ty : (1-X*C u : K[X]).natTrailingDegree = 0 := by
    apply natTrailingDegree_eq_zero.mpr
    right
    simp
  have ht := congrArg Polynomial.natTrailingDegree he
  rw [natTrailingDegree_mul (mul_ne_zero hx hsp) hh, natTrailingDegree_mul hx hsp,
    natTrailingDegree_mul (mul_ne_zero (mul_ne_zero X_ne_zero hy) hp) hsh,
    natTrailingDegree_mul (mul_ne_zero X_ne_zero hy) hp,
    natTrailingDegree_mul X_ne_zero hy, tx, ty, natTrailingDegree_X,
    trailing_rescale u hu p, trailing_rescale u hu h] at ht
  omega

#print axioms homogeneous_shift_zero
end
end GuoWang.Clear
```

### `GWOperatorCore.lean`

```lean
import GWShiftObstruction

/-! Coefficientwise local vanishing via the order-at-zero shift obstruction.
A scalar cyclotomic factor commutes with the parameter shift; apply once twice. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

def shiftOperator (u : R) (p h : Polynomial R) : Polynomial R :=
  (X-1)*rescale u p*h - X*(1-X*C u)*p*rescale u h

@[simp] lemma map_shiftOperator (f : R →+* S) (u : R) (p h : Polynomial R) :
    (shiftOperator u p h).map f = shiftOperator (f u) (p.map f) (h.map f) := by
  simp only [shiftOperator, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C, map_rescale]

lemma shiftOperator_C_mul (u c : R) (p h : Polynomial R) :
    shiftOperator u (C c*p) h = C c*shiftOperator u p h := by
  simp only [shiftOperator, rescale_C_mul]
  ring

lemma cyclotomic_dvd_of_operator {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {z : K} (hn : 0 < n) (hz : IsPrimitiveRoot z n)
    (u : ℚ[X]) (hu : aeval z u ≠ 0) (p h : Polynomial ℚ[X])
    (hh : h.map (aeval z).toRingHom ≠ 0)
    (hop : C (cyclotomic n ℚ) ∣ shiftOperator u p h) : C (cyclotomic n ℚ) ∣ p := by
  apply (C_cyclotomic_dvd_iff_map_zero hn hz p).mpr
  have he := (C_cyclotomic_dvd_iff_map_zero hn hz _).mp hop
  rw [map_shiftOperator] at he
  exact homogeneous_shift_zero _ hu _ _ hh (sub_eq_zero.mp he)

end
end GuoWang.Clear
```

### `GWOperator.lean`

```lean
import GWOperatorCore

namespace GuoWang.Clear
open Polynomial
noncomputable section

/-- Apply the first-order obstruction to the cyclotomic quotient once more. -/
theorem cyclotomic_sq_dvd_of_operator {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {z : K} (hn : 0 < n) (hz : IsPrimitiveRoot z n)
    (u : ℚ[X]) (hu : aeval z u ≠ 0) (p h : Polynomial ℚ[X])
    (hh : h.map (aeval z).toRingHom ≠ 0)
    (hop : C ((cyclotomic n ℚ)^2) ∣ shiftOperator u p h) : C ((cyclotomic n ℚ)^2) ∣ p := by
  let c : ℚ[X] := cyclotomic n ℚ
  have hc : (C c : Polynomial ℚ[X]) ≠ 0 := C_ne_zero.mpr (cyclotomic.monic n ℚ).ne_zero
  have hop' : (C c : Polynomial ℚ[X])*C c ∣ shiftOperator u p h := by
    simpa only [c, C_pow, pow_two, C_mul] using hop
  have h₁ : C c ∣ shiftOperator u p h :=
    dvd_trans (dvd_mul_right (C c) (C c)) hop'
  obtain ⟨r, hr⟩ := cyclotomic_dvd_of_operator hn hz u hu p h hh h₁
  have h₂ : C c ∣ shiftOperator u r h := by
    rw [hr, shiftOperator_C_mul] at hop'
    obtain ⟨v, hv⟩ := hop'
    refine ⟨v, ?_⟩
    apply mul_left_cancel₀ hc
    simpa only [mul_assoc] using hv
  obtain ⟨v, hv⟩ := cyclotomic_dvd_of_operator hn hz u hu r h hh h₂
  refine ⟨v, ?_⟩
  rw [hr, hv, C_pow, pow_two, mul_assoc]

/-- Ready-to-use application for the actual numerator and its proved generic
root-regular denominator. The boundary operator input is still explicit. -/
theorem P_sq_dvd_of_operator {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {z : K} (hn : 0 < n) (hz : IsPrimitiveRoot z n) (h4 : n % 4 = 1)
    (hop : C ((cyclotomic n ℚ)^2) ∣ shiftOperator ((X : ℚ[X])^4) (P n) (H n)) :
    C ((cyclotomic n ℚ)^2) ∣ P n := by
  apply cyclotomic_sq_dvd_of_operator hn hz _ _ _ _ (H_at_root_ne_zero hz h4) hop
  simpa using pow_ne_zero 4 (hz.ne_zero hn.ne')

#print axioms cyclotomic_sq_dvd_of_operator
#print axioms P_sq_dvd_of_operator
end
end GuoWang.Clear
```

### `GWAssemble.lean`

```lean
import GWCyclotomic

/-! Assembly for the literal modulus, with mathematical inputs left explicit.
This module does not declare the universal endpoint. -/
namespace GuoWang
open Polynomial
open scoped BigOperators
noncomputable section

/-- The proper-divisor factors and fourth top factor give exactly [n]Φ_n³. -/
theorem assemble_modulus (n : ℕ) (hn : 0 < n) (hlarge : 1 < n)
    (f : ℚ[X]) (htop : (cyclotomic n ℚ)^4 ∣ f)
    (hproper : ∀ d : ℕ, d ∣ n → 1 < d → d < n → cyclotomic d ℚ ∣ f) :
    qIntPoly n * (cyclotomic n ℚ)^3 ∣ f := by
  let s := (n.divisors.erase 1).erase n
  have hmem : n ∈ n.divisors.erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors_self n hn.ne'⟩
  have hs (d : ℕ) (hd : d ∈ s) : d ∣ n ∧ 1 < d ∧ d < n := by
    obtain ⟨hdn, hd⟩ := Finset.mem_erase.mp hd
    obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hpos : 0 < d := Nat.pos_of_mem_divisors hd
    exact ⟨hdvd, by omega, lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hdn⟩
  have hprod : (∏ d ∈ s, cyclotomic d ℚ) ∣ f := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact cyclotomic.isCoprime_rat hij
    · intro d hd
      exact hproper d (hs d hd).1 (hs d hd).2.1 (hs d hd).2.2
  have hcop : IsCoprime (∏ d ∈ s, cyclotomic d ℚ) ((cyclotomic n ℚ)^4) := by
    apply IsCoprime.prod_left_iff.mpr
    intro d hd
    exact (cyclotomic.isCoprime_rat (by have := hs d hd; omega)).pow_right
  have he : (∏ d ∈ s, cyclotomic d ℚ) * cyclotomic n ℚ = qIntPoly n := by
    simpa only [s, qIntPoly, prod_cyclotomic_eq_geom_sum hn ℚ] using
      (Finset.prod_erase_mul (n.divisors.erase 1) (cyclotomic · ℚ) hmem)
  have ha := hcop.mul_dvd hprod htop
  have he' : qIntPoly n * (cyclotomic n ℚ)^3 =
      (∏ d ∈ s, cyclotomic d ℚ) * (cyclotomic n ℚ)^4 := by rw [← he]; ring
  rw [he']
  exact ha

#print axioms assemble_modulus
end
end GuoWang
```

### `GWAuditR3.lean`

```lean
import GWShiftProducts
import GWFieldTerms
import GWFieldShiftA
import GWFieldShiftB
import GWFieldLegal
import GWFieldNext
import GWFieldRecurrence
import GWBoundaryAlgebra
import GWBoundaryTerms
import GWBoundaryA
import GWBoundaryB
import GWCancelledBoundary
import GWIndependent
import GWInverseRoot
import GWExtractFourth
import GWResidueProducts
import GWShiftObstruction
import GWOperatorCore
import GWOperator
import GWAssemble

/-! Full stage-3 theorem type and transitive axiom inventory. -/
#eval Lean.versionString
#check @GuoWang.guo_wang_conj_4_1_one
#print axioms GuoWang.guo_wang_conj_4_1_one
#check @GuoWang.WZ.poch_backward_two_ratio
#print axioms GuoWang.WZ.poch_backward_two_ratio
#check @GuoWang.WZ.pair_shift_two
#print axioms GuoWang.WZ.pair_shift_two
#check @GuoWang.WZ.pair_shift_four
#print axioms GuoWang.WZ.pair_shift_four
#check @GuoWang.WZ.pair_den_shift
#print axioms GuoWang.WZ.pair_den_shift
#check @GuoWang.WZ.ft_eq_term
#print axioms GuoWang.WZ.ft_eq_term
#check @GuoWang.WZ.pd_shift
#print axioms GuoWang.WZ.pd_shift
#check @GuoWang.WZ.ft_shift_A
#print axioms GuoWang.WZ.ft_shift_A
#check @GuoWang.WZ.ft_shift_B
#print axioms GuoWang.WZ.ft_shift_B
#check @GuoWang.WZ.Good.one_sub
#print axioms GuoWang.WZ.Good.one_sub
#check @GuoWang.WZ.Good.one_div
#print axioms GuoWang.WZ.Good.one_div
#check @GuoWang.WZ.Good.inv_sub
#print axioms GuoWang.WZ.Good.inv_sub
#check @GuoWang.WZ.Good.shift
#print axioms GuoWang.WZ.Good.shift
#check @GuoWang.WZ.Good.pd_ne
#print axioms GuoWang.WZ.Good.pd_ne
#check @GuoWang.WZ.Good.den_ne
#print axioms GuoWang.WZ.Good.den_ne
#check @GuoWang.WZ.Good.qInt_eq
#print axioms GuoWang.WZ.Good.qInt_eq
#check @GuoWang.WZ.Good.qInt_ne
#print axioms GuoWang.WZ.Good.qInt_ne
#check @GuoWang.WZ.Good.qInt_ratio
#print axioms GuoWang.WZ.Good.qInt_ratio
#check @GuoWang.WZ.eval_factor
#print axioms GuoWang.WZ.eval_factor
#check @GuoWang.WZ.factor_quotient
#print axioms GuoWang.WZ.factor_quotient
#check @GuoWang.WZ.ft_next_A
#print axioms GuoWang.WZ.ft_next_A
#check @GuoWang.WZ.ft_next_B
#print axioms GuoWang.WZ.ft_next_B
#check @GuoWang.WZ.Good.qfactor
#print axioms GuoWang.WZ.Good.qfactor
#check @GuoWang.WZ.Good.afactor
#print axioms GuoWang.WZ.Good.afactor
#check @GuoWang.WZ.Good.divfactor
#print axioms GuoWang.WZ.Good.divfactor
#check @GuoWang.WZ.Good.diffactor
#print axioms GuoWang.WZ.Good.diffactor
#check @GuoWang.WZ.fa_step
#print axioms GuoWang.WZ.fa_step
#check @GuoWang.WZ.fb_step
#print axioms GuoWang.WZ.fb_step
#check @GuoWang.WZ.ga_zero
#print axioms GuoWang.WZ.ga_zero
#check @GuoWang.WZ.gb_zero
#print axioms GuoWang.WZ.gb_zero
#check @GuoWang.WZ.fd_recurrence
#print axioms GuoWang.WZ.fd_recurrence
#check @GuoWang.WZ.cancel_boundary
#print axioms GuoWang.WZ.cancel_boundary
#check @GuoWang.WZ.ga_cancelled
#print axioms GuoWang.WZ.ga_cancelled
#check @GuoWang.WZ.gb_cancelled
#print axioms GuoWang.WZ.gb_cancelled
#check @GuoWang.WZ.fd_cancelled_recurrence
#print axioms GuoWang.WZ.fd_cancelled_recurrence
#check @GuoWang.WZ.linear_generic_ne
#print axioms GuoWang.WZ.linear_generic_ne
#check @GuoWang.WZ.generic_good
#print axioms GuoWang.WZ.generic_good
#check @GuoWang.WZ.fa_scalar
#print axioms GuoWang.WZ.fa_scalar
#check @GuoWang.WZ.fb_scalar
#print axioms GuoWang.WZ.fb_scalar
#check @GuoWang.WZ.fd_scalar
#print axioms GuoWang.WZ.fd_scalar
#check @GuoWang.WZ.fd_fraction
#print axioms GuoWang.WZ.fd_fraction
#check @GuoWang.WZ.generic_recurrence
#print axioms GuoWang.WZ.generic_recurrence
#check @GuoWang.Clear.inverseNumerator_map
#print axioms GuoWang.Clear.inverseNumerator_map
#check @GuoWang.Clear.inverseNumerator_at_root
#print axioms GuoWang.Clear.inverseNumerator_at_root
#check @GuoWang.Clear.inverse_root_specializes
#print axioms GuoWang.Clear.inverse_root_specializes
#check @GuoWang.Clear.spec_positive
#print axioms GuoWang.Clear.spec_positive
#check @GuoWang.Clear.positive_ne_inverse
#print axioms GuoWang.Clear.positive_ne_inverse
#check @GuoWang.Clear.fourth_of_parameter_roots
#print axioms GuoWang.Clear.fourth_of_parameter_roots
#check @GuoWang.Clear.top_fourth_of_parameter_roots
#print axioms GuoWang.Clear.top_fourth_of_parameter_roots
#check @GuoWang.Residues.complete_product
#print axioms GuoWang.Residues.complete_product
#check @GuoWang.Residues.complete_polynomial
#print axioms GuoWang.Residues.complete_polynomial
#check @GuoWang.Residues.deleted_product
#print axioms GuoWang.Residues.deleted_product
#check @GuoWang.Clear.coeff_rescale
#print axioms GuoWang.Clear.coeff_rescale
#check @GuoWang.Clear.trailing_rescale
#print axioms GuoWang.Clear.trailing_rescale
#check @GuoWang.Clear.homogeneous_shift_zero
#print axioms GuoWang.Clear.homogeneous_shift_zero
#check @GuoWang.Clear.map_shiftOperator
#print axioms GuoWang.Clear.map_shiftOperator
#check @GuoWang.Clear.shiftOperator_C_mul
#print axioms GuoWang.Clear.shiftOperator_C_mul
#check @GuoWang.Clear.cyclotomic_dvd_of_operator
#print axioms GuoWang.Clear.cyclotomic_dvd_of_operator
#check @GuoWang.Clear.cyclotomic_sq_dvd_of_operator
#print axioms GuoWang.Clear.cyclotomic_sq_dvd_of_operator
#check @GuoWang.Clear.P_sq_dvd_of_operator
#print axioms GuoWang.Clear.P_sq_dvd_of_operator
#check @GuoWang.assemble_modulus
#print axioms GuoWang.assemble_modulus
```

### `GWBoundaryPolys.lean`

```lean
import GWCancelledBoundary
import GWIndependent
import GWOperator

/-! Polynomial forms of the cancelled boundaries. The only inverse cleared
here is a power of the parameter, and its nonvanishing is explicit. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

def boundaryBase (q : R) (N : ℕ) : R[X] :=
  C (1-q) * (∏ j ∈ Finset.range N, (1-X*C (q^(4+4*j)))) *
    ∏ j ∈ Finset.range (N-1), ((X-C (q^(4+4*j)))*C (1-q^(4+4*j)))

def boundaryC (q : R) : R[X] := (1-X*C (q^4))*(1-X^2*C (q^4))
def boundaryNum (q : R) (N s e : ℕ) (sign : R) : R[X] :=
  C (sign*q^e) * boundaryC q * pairPoch q 1 s N

def boundaryDA (q : R) (N : ℕ) : R[X] :=
  boundaryBase q N * (X*C (q^3)-C (q^(2*N))) * (X*C q-C (q^(2*N)))
def boundaryDB (q : R) (N : ℕ) : R[X] :=
  boundaryBase q N * (X*C (q^3)-C (q^(4*N))) * (1-X*C q)

def boundaryNA (q : R) (N : ℕ) := boundaryNum q N 2 (3*N^2) ((-1)^(N+1))
def boundaryNB (q : R) (N : ℕ) := boundaryNum q N 4 (2*N^2+N) ((-1)^N)

@[simp] lemma map_boundaryBase {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    (boundaryBase q N).map f = boundaryBase (f q) N := by
  simp [boundaryBase, Polynomial.map_prod]
@[simp] lemma map_boundaryDA {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    (boundaryDA q N).map f = boundaryDA (f q) N := by simp [boundaryDA]
@[simp] lemma map_boundaryDB {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    (boundaryDB q N).map f = boundaryDB (f q) N := by simp [boundaryDB]
@[simp] lemma map_boundaryNA {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    (boundaryNA q N).map f = boundaryNA (f q) N := by
  simp [boundaryNA, boundaryNum, boundaryC]
@[simp] lemma map_boundaryNB {S : Type*} [CommRing S] (f : R →+* S) (q : R) (N : ℕ) :
    (boundaryNB q N).map f = boundaryNB (f q) N := by
  simp [boundaryNB, boundaryNum, boundaryC]

section Field
variable {K : Type*} [Field K]

lemma eval_boundaryBase (q a : K) (N : ℕ) (ha : a ≠ 0) :
    (boundaryBase q N).eval a = a^(N-1)*GuoWang.WZ.boundaryDen q a N := by
  simp only [boundaryBase, eval_mul, eval_C, eval_prod, eval_sub, eval_X,
    eval_one]
  have htail : (∏ j ∈ Finset.range (N-1), ((a-q^(4+4*j))*(1-q^(4+4*j)))) =
      a^(N-1) * (QWZCore.poch (q^4/a) (q^4) (N-1) *
        QWZCore.poch (q^4) (q^4) (N-1)) := by
    have he : a^(N-1) = ∏ _j ∈ Finset.range (N-1), a := by simp
    rw [he]
    simp only [QWZCore.poch, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, pow_add]
    field_simp
  rw [htail]
  have hhead : (∏ j ∈ Finset.range N, (1-a*q^(4+4*j))) =
      QWZCore.poch (a*q^4) (q^4) N := by
    simp only [QWZCore.poch, ← pow_mul, pow_add, mul_assoc]
  rw [hhead]
  unfold GuoWang.WZ.boundaryDen
  ring

lemma eval_boundaryNum (q a : K) (N s e : ℕ) (sign : K) (ha : a ≠ 0) :
    (boundaryNum q N s e sign).eval a = a^N *
      (sign*GuoWang.WZ.c q a*q^e*
        (GuoWang.WZ.pair q a 1 s N * QWZCore.poch q (q^s) N)) := by
  simp only [boundaryNum, eval_mul, eval_C, boundaryC, eval_sub, eval_one,
    eval_pow, eval_X, eval_pairPoch_field q a 1 s N ha, pow_one]
  unfold GuoWang.WZ.c GuoWang.WZ.pair
  ring

lemma ca_fraction (q a : K) (N : ℕ) (hN : 0 < N) (ha : a ≠ 0) :
    GuoWang.WZ.ca q a N =
      (boundaryNA q N).eval a / (a*(boundaryDA q N).eval a) := by
  rw [boundaryNA, eval_boundaryNum q a N 2 _ _ ha]
  simp only [boundaryDA, eval_mul, eval_sub, eval_X, eval_C, eval_boundaryBase q a N ha]
  rw [show a*(a^(N-1)*GuoWang.WZ.boundaryDen q a N*(a*q^3-q^(2*N))*(a*q-q^(2*N))) =
      a^N * (GuoWang.WZ.boundaryDen q a N*(a*q^3-q^(2*N))*(a*q-q^(2*N))) by
        have hp : a^N = a^(N-1)*a := by
          conv_lhs => rw [show N = N-1+1 by omega]
          rw [pow_succ]
        rw [hp]; ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero N ha)]
  rfl

lemma cb_fraction (q a : K) (N : ℕ) (hN : 0 < N) (ha : a ≠ 0) :
    GuoWang.WZ.cb q a N =
      (boundaryNB q N).eval a / (a*(boundaryDB q N).eval a) := by
  rw [boundaryNB, eval_boundaryNum q a N 4 _ _ ha]
  simp only [boundaryDB, eval_mul, eval_sub, eval_X, eval_C, eval_one,
    eval_boundaryBase q a N ha]
  rw [show a*(a^(N-1)*GuoWang.WZ.boundaryDen q a N*(a*q^3-q^(4*N))*(1-a*q)) =
      a^N * (GuoWang.WZ.boundaryDen q a N*(a*q^3-q^(4*N))*(1-a*q)) by
        have hp : a^N = a^(N-1)*a := by
          conv_lhs => rw [show N = N-1+1 by omega]
          rw [pow_succ]
        rw [hp]; ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero N ha)]
  rfl

end Field
end
end GuoWang.Clear
```

### `GWBoundaryClear.lean`

```lean
import GWBoundaryPolys

namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {K : Type*} [Field K]

lemma boundaryBase_good (q a : K) (h : GuoWang.WZ.Good q a) (N : ℕ) :
    (boundaryBase q N).eval a ≠ 0 := by
  simp only [boundaryBase, eval_mul, eval_C, eval_sub, eval_prod, eval_one, eval_X]
  apply mul_ne_zero
  · apply mul_ne_zero (by simpa using h.pow_ne 1 (by omega))
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => h.one_sub _)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact mul_ne_zero (by simpa using h.param_ne 0 (4+4*j)) (h.pow_ne _ (by omega))

lemma boundaryDA_good (q a : K) (h : GuoWang.WZ.Good q a) (N : ℕ) :
    (boundaryDA q N).eval a ≠ 0 := by
  simp only [boundaryDA, eval_mul, eval_sub, eval_C, eval_X]
  exact mul_ne_zero (mul_ne_zero (boundaryBase_good q a h N) (h.param_ne _ _))
    (by simpa using h.param_ne 1 (2*N))

lemma boundaryDB_good (q a : K) (h : GuoWang.WZ.Good q a) (N : ℕ) :
    (boundaryDB q N).eval a ≠ 0 := by
  simp only [boundaryDB, eval_mul, eval_sub, eval_C, eval_X, eval_one]
  exact mul_ne_zero (mul_ne_zero (boundaryBase_good q a h N) (h.param_ne _ _))
    (by simpa using h.one_sub 1)

/-- No certificate poles survive in this polynomial identity. -/
theorem cleared_recurrence_value (q a : K) (h : GuoWang.WZ.Good q a)
    (N : ℕ) (hN : 0 < N) :
    (shiftOperator (q^4) (commonNum q N) (commonDen q N)).eval a *
      (boundaryDA q N).eval a * (boundaryDB q N).eval a =
    (commonDen q N).eval a * (commonDen q N).eval (a*q^4) *
      ((boundaryNA q N).eval a * (boundaryDB q N).eval a -
        (boundaryNB q N).eval a * (boundaryDA q N).eval a) := by
  have he := GuoWang.WZ.fd_cancelled_recurrence q a h N hN
  rw [GuoWang.WZ.fd_fraction q _ h.shift, GuoWang.WZ.fd_fraction q a h,
    ca_fraction q a N hN h.a_ne, cb_fraction q a N hN h.a_ne] at he
  have hd : (commonDen q N).eval a ≠ 0 := by
    simp only [commonDen, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => h.den_ne k)
  have hs : (commonDen q N).eval (a*q^4) ≠ 0 := by
    simp only [commonDen, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => h.shift.den_ne k)
  simp only [shiftOperator, eval_sub, eval_mul, eval_X, eval_one, eval_C, eval_rescale]
  field_simp [h.a_ne, hd, hs, boundaryDA_good q a h N, boundaryDB_good q a h N] at he
  linear_combination he

end
end GuoWang.Clear
```

### `GWPolynomialRecurrence.lean`

```lean
import GWBoundaryClear

/-! The generic field identity descends to ℚ[q][a]. Every later specialization
is a ring homomorphism on this identity, including terminating parameters. -/
namespace GuoWang.Clear
open Polynomial
noncomputable section
open GuoWang.WZ

lemma eval_generic (p : Polynomial F) :
    (p.map (algebraMap F E)).eval genericA = algebraMap F[X] E p := by
  rw [eval_map]
  exact RatFunc.aeval_X_left_eq_algebraMap p

/-- Cleared recurrence with no generic-legality hypothesis and no division. -/
theorem polynomial_recurrence (N : ℕ) (hN : 0 < N) :
    shiftOperator ((X : ℚ[X])^4) (P N) (H N) *
      boundaryDA (X : ℚ[X]) N * boundaryDB (X : ℚ[X]) N =
    H N * rescale ((X : ℚ[X])^4) (H N) *
      (boundaryNA (X : ℚ[X]) N * boundaryDB (X : ℚ[X]) N -
        boundaryNB (X : ℚ[X]) N * boundaryDA (X : ℚ[X]) N) := by
  apply Polynomial.map_injective qMap (RatFunc.algebraMap_injective ℚ)
  apply RatFunc.algebraMap_injective F
  rw [← eval_generic, ← eval_generic]
  have he := cleared_recurrence_value genericQ genericA generic_good N hN
  simpa only [Polynomial.map_mul, Polynomial.map_sub, map_shiftOperator, map_commonNum,
    map_commonDen, P, H, map_boundaryDA, map_boundaryDB, map_boundaryNA, map_boundaryNB,
    map_rescale, map_pow, RatFunc.algebraMap_X, eval_mul, eval_sub, eval_rescale,
    genericQ, GuoWang.X'] using he

/-- Direct value form for every specialization; no pole-sensitive evaluation
of rational functions occurs. -/
theorem specialized_recurrence (N : ℕ) (hN : 0 < N) (a : RatFunc ℚ) :
    ((a-1)*spec (a*GuoWang.X'^4) (P N)*spec a (H N) -
      a*(1-a*GuoWang.X'^4)*spec a (P N)*spec (a*GuoWang.X'^4) (H N)) *
      spec a (boundaryDA (X : ℚ[X]) N) * spec a (boundaryDB (X : ℚ[X]) N) =
    spec a (H N) * spec (a*GuoWang.X'^4) (H N) *
      (spec a (boundaryNA (X : ℚ[X]) N) * spec a (boundaryDB (X : ℚ[X]) N) -
        spec a (boundaryNB (X : ℚ[X]) N) * spec a (boundaryDA (X : ℚ[X]) N)) := by
  have he := congrArg (spec a) (polynomial_recurrence N hN)
  simpa only [map_mul, map_sub, shiftOperator, spec, coe_eval₂RingHom,
    eval₂_sub, eval₂_mul, eval₂_X, eval₂_one, eval₂_C, eval₂_rescale,
    map_pow, RatFunc.algebraMap_X, GuoWang.X'] using he

#print axioms polynomial_recurrence
#print axioms specialized_recurrence
end
end GuoWang.Clear
```

### `GWTerminatingBoundary.lean`

```lean
import GWPolynomialRecurrence

namespace GuoWang.Clear
open Polynomial
noncomputable section

lemma spec_boundaryBase (a : RatFunc ℚ) (N : ℕ) :
    spec a (boundaryBase (X : ℚ[X]) N) = (boundaryBase GuoWang.X' N).eval a := by
  simp only [spec, coe_eval₂RingHom, ← eval_map, map_boundaryBase]
  rfl
lemma spec_boundaryDA (a : RatFunc ℚ) (N : ℕ) :
    spec a (boundaryDA (X : ℚ[X]) N) = (boundaryDA GuoWang.X' N).eval a := by
  simp only [spec, coe_eval₂RingHom, ← eval_map, map_boundaryDA]
  rfl
lemma spec_boundaryDB (a : RatFunc ℚ) (N : ℕ) :
    spec a (boundaryDB (X : ℚ[X]) N) = (boundaryDB GuoWang.X' N).eval a := by
  simp only [spec, coe_eval₂RingHom, ← eval_map, map_boundaryDB]
  rfl

lemma boundaryBase_qpow_ne (N e : ℕ) (he : e % 4 = 1) :
    spec (GuoWang.X'^e) (boundaryBase (X : ℚ[X]) N) ≠ 0 := by
  rw [spec_boundaryBase]
  simp only [boundaryBase, eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_X]
  apply mul_ne_zero
  · apply mul_ne_zero (by simpa using GuoWang.one_sub_X'_pow_ne_zero 1 (by omega))
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    rw [← pow_add]
    exact GuoWang.one_sub_X'_pow_ne_zero _ (by omega)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply mul_ne_zero
    · exact sub_ne_zero.mpr (fun h => by have := GuoWang.X'_pow_injective h; omega)
    · exact GuoWang.one_sub_X'_pow_ne_zero _ (by omega)

lemma boundaryDA_qpow_ne (N e : ℕ) (he : e % 4 = 1) (hbound : e+3 < 2*N) :
    spec (GuoWang.X'^e) (boundaryDA (X : ℚ[X]) N) ≠ 0 := by
  have hb := boundaryBase_qpow_ne N e he
  rw [spec_boundaryBase] at hb
  rw [spec_boundaryDA]
  simp only [boundaryDA, eval_mul, eval_sub, eval_X, eval_C, ← pow_add]
  apply mul_ne_zero (mul_ne_zero hb (sub_ne_zero.mpr (fun h => by
    have := GuoWang.X'_pow_injective h; omega)))
  rw [show GuoWang.X'^e*GuoWang.X' = GuoWang.X'^(e+1) by rw [pow_succ]]
  exact sub_ne_zero.mpr (fun h => by have := GuoWang.X'_pow_injective h; omega)

lemma boundaryDB_qpow_ne (N e : ℕ) (he : e % 4 = 1) (hbound : e+3 < 4*N) :
    spec (GuoWang.X'^e) (boundaryDB (X : ℚ[X]) N) ≠ 0 := by
  have hb := boundaryBase_qpow_ne N e he
  rw [spec_boundaryBase] at hb
  rw [spec_boundaryDB]
  simp only [boundaryDB, eval_mul, eval_sub, eval_X, eval_C, eval_one, ← pow_add]
  apply mul_ne_zero (mul_ne_zero hb (sub_ne_zero.mpr (fun h => by
    have := GuoWang.X'_pow_injective h; omega)))
  rw [show GuoWang.X'^e*GuoWang.X' = GuoWang.X'^(e+1) by rw [pow_succ]]
  exact GuoWang.one_sub_X'_pow_ne_zero _ (by omega)

lemma boundaryNA_terminates (N j : ℕ) (hj : 2*j < N) :
    spec (GuoWang.X'^(4*j+1)) (boundaryNA (X : ℚ[X]) N) = 0 := by
  simp only [spec, coe_eval₂RingHom, ← eval_map, map_boundaryNA]
  change (boundaryNA GuoWang.X' N).eval _ = 0
  rw [boundaryNA, eval_boundaryNum _ _ _ _ _ _ (pow_ne_zero _ GuoWang.X'_ne_zero)]
  unfold GuoWang.WZ.pair
  simp only [pow_one]
  rw [← GuoWang.poch_eq_core, ← GuoWang.poch_eq_core,
    GuoWang.terminating_A_poch_zero j N hj]
  ring

lemma boundaryNB_terminates (N j : ℕ) (hj : j < N) :
    spec (GuoWang.X'^(4*j+1)) (boundaryNB (X : ℚ[X]) N) = 0 := by
  simp only [spec, coe_eval₂RingHom, ← eval_map, map_boundaryNB]
  change (boundaryNB GuoWang.X' N).eval _ = 0
  rw [boundaryNB, eval_boundaryNum _ _ _ _ _ _ (pow_ne_zero _ GuoWang.X'_ne_zero)]
  unfold GuoWang.WZ.pair
  simp only [pow_one]
  rw [← GuoWang.poch_eq_core, ← GuoWang.poch_eq_core,
    GuoWang.terminating_B_poch_zero j N hj]
  ring

#print axioms boundaryDA_qpow_ne
#print axioms boundaryDB_qpow_ne
#print axioms boundaryNA_terminates
#print axioms boundaryNB_terminates
end
end GuoWang.Clear
```

### `GWTerminatingRoots.lean`

```lean
import GWTerminatingBoundary

namespace GuoWang.Clear
open Polynomial
noncomputable section

/-- Induction uses only the cancelled polynomial identity. -/
theorem at_P_terminating (N j : ℕ) (hj : 4*j+1 ≤ N) :
    spec (GuoWang.X'^(4*j+1)) (P N) = 0 := by
  induction j with
  | zero => simpa only [Nat.mul_zero, Nat.zero_add, pow_one] using at_P_q N
  | succ j ih =>
    have hz := ih (by omega)
    have hn : 0 < N := by omega
    have he := specialized_recurrence N hn (GuoWang.X'^(4*j+1))
    rw [hz, boundaryNA_terminates N j (by omega), boundaryNB_terminates N j (by omega)] at he
    have ha : GuoWang.X'^(4*j+1)-1 ≠ 0 := by
      exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp
        (GuoWang.one_sub_X'_pow_ne_zero _ (by omega))))
    have hdA := boundaryDA_qpow_ne N (4*j+1) (by omega) (by omega)
    have hdB := boundaryDB_qpow_ne N (4*j+1) (by omega) (by omega)
    have hh := at_H_qpow_ne_zero N (4*j+1) (by omega)
    simp only [mul_zero, zero_mul, sub_zero] at he
    have hz' : spec (GuoWang.X'^(4*j+1)*GuoWang.X'^4) (P N) = 0 := by
      rcases mul_eq_zero.mp he with he | he
      · rcases mul_eq_zero.mp he with he | he
        · rcases mul_eq_zero.mp he with he | he
          · exact (mul_eq_zero.mp he).resolve_left ha
          · exact False.elim (hh he)
        · exact False.elim (hdA he)
      · exact False.elim (hdB he)
    convert hz' using 1
    rw [← pow_add]
    congr 2

theorem at_P_qn (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    spec (GuoWang.X'^n) (P n) = 0 := by
  have he : 4*((n-1)/4)+1 = n := by omega
  simpa only [he] using at_P_terminating n ((n-1)/4) (by omega)

end
end GuoWang.Clear

namespace GuoWang
lemma A_inverse (q a : RatFunc ℚ) (k : ℕ) : A q a⁻¹ k = A q a k := by
  simp only [A, paramDen_inv, div_eq_mul_inv, inv_inv]
  ring
lemma B_inverse (q a : RatFunc ℚ) (k : ℕ) : B q a⁻¹ k = B q a k := by
  simp only [B, paramDen_inv, div_eq_mul_inv, inv_inv]
  ring
lemma D_inverse (N : ℕ) (q a : RatFunc ℚ) : D N q a⁻¹ = D N q a := by
  simp only [D, A_inverse, B_inverse]
end GuoWang

namespace GuoWang.Clear

theorem at_P_qn_inverse (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    spec (GuoWang.X'^n)⁻¹ (P n) = 0 := by
  have hz : GuoWang.D n GuoWang.X' (GuoWang.X'^n) = 0 :=
    (at_P_eq_zero_iff n _ (pow_ne_zero _ GuoWang.X'_ne_zero)
      (fun k _ => GuoWang.paramDen_qpow_ne_zero n k h4)).mp (at_P_qn n hn h4)
  apply (at_P_eq_zero_iff n _ (inv_ne_zero (pow_ne_zero _ GuoWang.X'_ne_zero))
    (fun k _ => GuoWang.paramDen_qpow_inv_ne_zero n k h4)).mpr
  rw [GuoWang.D_inverse, hz]

#print axioms at_P_terminating
#print axioms at_P_qn
#print axioms at_P_qn_inverse
end GuoWang.Clear
```

### `GWDeletedBoundary.lean`

```lean
import GWPolynomialRecurrence
import GWResidueProducts

namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

def parameterPair (q : R) (s N : ℕ) : R[X] :=
  ∏ j ∈ Finset.range N, ((1-X*C (q^(1+s*j)))*(X-C (q^(1+s*j))))

def deletedBoundary (q : R) (N s e j₀ : ℕ) (sign : R) : R[X] :=
  C (sign*q^e*(∏ j ∈ (Finset.range N).erase j₀, (1-q^(1+s*j)))) *
    boundaryC q * parameterPair q s N

lemma pairPoch_split (q : R) (s N : ℕ) :
    pairPoch q 1 s N = parameterPair q s N * C (∏ j ∈ Finset.range N, (1-q^(1+s*j))) := by
  simp only [pairPoch, parameterPair, map_prod, ← Finset.prod_mul_distrib]

lemma boundary_factor (q : R) (N s e j₀ : ℕ) (sign : R)
    (hj : j₀ < N) (he : 1+s*j₀ = N) :
    boundaryNum q N s e sign = C (1-q^N)*deletedBoundary q N s e j₀ sign := by
  have hp := Finset.mul_prod_erase (Finset.range N) (fun j => 1-q^(1+s*j))
    (Finset.mem_range.mpr hj)
  rw [he] at hp
  rw [boundaryNum, pairPoch_split, ← hp]
  simp only [deletedBoundary, map_mul]
  ring

@[simp] lemma map_parameterPair {S : Type*} [CommRing S] (f : R →+* S) (q : R) (s N : ℕ) :
    (parameterPair q s N).map f = parameterPair (f q) s N := by
  simp [parameterPair, Polynomial.map_prod]
@[simp] lemma map_deletedBoundary {S : Type*} [CommRing S] (f : R →+* S)
    (q : R) (N s e j₀ : ℕ) (sign : R) :
    (deletedBoundary q N s e j₀ sign).map f = deletedBoundary (f q) N s e j₀ (f sign) := by
  simp [deletedBoundary, boundaryC, Polynomial.map_prod]

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K} {n : ℕ}

lemma parameterPair_root (hz : IsPrimitiveRoot z n) (hn : 0 < n)
    (s : ℕ) (hs : n.Coprime s) :
    parameterPair z s n = (1-X^n)*(X^n-1) := by
  unfold parameterPair
  rw [Finset.prod_mul_distrib, GuoWang.Residues.complete_polynomial hz hn s hs]
  congr 1
  have he := X_pow_sub_C_eq_prod (hz.pow_of_coprime s hs.symm) hn
    (α := z) (a := (1:K)) hz.pow_eq_one
  rw [C_1] at he
  rw [he]
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  rw [pow_add, pow_one, pow_mul]
  ring

lemma deletedBoundary_root (hz : IsPrimitiveRoot z n) (hn : 0 < n)
    (s e j₀ : ℕ) (hs : n.Coprime s) (hj : j₀ < n) (hj₀ : 1+s*j₀ = n)
    (he : n ∣ e) (sign : K) :
    deletedBoundary z n s e j₀ sign =
      C (sign*(n:K)) * boundaryC z * ((1-X^n)*(X^n-1)) := by
  have hzj : z^(1+s*j₀) = 1 := by rw [hj₀, hz.pow_eq_one]
  rw [deletedBoundary, GuoWang.Residues.deleted_product hz hn s hs j₀ hj hzj,
    (hz.pow_eq_one_iff_dvd e).mpr he, mul_one, parameterPair_root hz hn s hs]

end Roots
end
end GuoWang.Clear
```

### `GWBoundaryRootMatch.lean`

```lean
import GWDeletedBoundary
import Mathlib.RingTheory.Polynomial.Basic

namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K} {n : ℕ}

lemma coprime_four (h4 : n % 4 = 1) : n.Coprime 4 := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm n 4, Nat.gcd_rec, h4]
  decide
lemma coprime_two (h4 : n % 4 = 1) : n.Coprime 2 :=
  (coprime_four h4).of_dvd_right (by decide)

lemma deleted_match (hz : IsPrimitiveRoot z n) (hn : 0 < n) (h4 : n % 4 = 1) :
    deletedBoundary z n 2 (3*n^2) ((n-1)/2) ((-1:K)^(n+1)) * boundaryDB z n -
    deletedBoundary z n 4 (2*n^2+n) ((n-1)/4) ((-1:K)^n) * boundaryDA z n = 0 := by
  rw [deletedBoundary_root hz hn 2 _ _ (coprime_two h4) (by omega) (by omega)
      (dvd_mul_of_dvd_right (dvd_pow_self n (by omega : 2 ≠ 0)) 3),
    deletedBoundary_root hz hn 4 _ _ (coprime_four h4) (by omega) (by omega)
      (dvd_add (dvd_mul_of_dvd_right (dvd_pow_self n (by omega : 2 ≠ 0)) 2) (dvd_refl n))]
  have ho : Odd n := ⟨2*(n/4), by omega⟩
  have hev : Even (n+1) := ⟨2*(n/4)+1, by omega⟩
  rw [ho.neg_one_pow, hev.neg_one_pow]
  have h2 : z^(2*n) = 1 := by rw [mul_comm 2 n, pow_mul, hz.pow_eq_one, one_pow]
  have h4' : z^(4*n) = 1 := by rw [mul_comm 4 n, pow_mul, hz.pow_eq_one, one_pow]
  simp only [one_mul, neg_mul, C_neg, C_1,
    boundaryDA, boundaryDB, h2, h4']
  ring

end
end GuoWang.Clear
```

### `GWBoundaryMatch.lean`

```lean
import GWBoundaryRootMatch

namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K} {n : ℕ}

/-- Each cancelled boundary has the same first-order coefficient at the root. -/
theorem boundary_cross_sq (hz : IsPrimitiveRoot z n) (hn : 0 < n) (h4 : n % 4 = 1) :
    C ((cyclotomic n ℚ)^2) ∣
      boundaryNA (X : ℚ[X]) n * boundaryDB (X : ℚ[X]) n -
      boundaryNB (X : ℚ[X]) n * boundaryDA (X : ℚ[X]) n := by
  let ua := deletedBoundary (X : ℚ[X]) n 2 (3*n^2) ((n-1)/2) ((-1)^(n+1))
  let ub := deletedBoundary (X : ℚ[X]) n 4 (2*n^2+n) ((n-1)/4) ((-1)^n)
  have hna : boundaryNA (X : ℚ[X]) n = C (1-(X : ℚ[X])^n)*ua :=
    boundary_factor _ n 2 _ _ _ (by omega) (by omega)
  have hnb : boundaryNB (X : ℚ[X]) n = C (1-(X : ℚ[X])^n)*ub :=
    boundary_factor _ n 4 _ _ _ (by omega) (by omega)
  have hfirst : cyclotomic n ℚ ∣ 1-(X : ℚ[X])^n := by
    apply (cyclotomic_dvd_iff_root hn hz _).mpr
    simp only [map_sub, map_one, map_pow, aeval_X, hz.pow_eq_one, sub_self]
  have hsecond : C (cyclotomic n ℚ) ∣
      ua*boundaryDB (X : ℚ[X]) n - ub*boundaryDA (X : ℚ[X]) n := by
    apply (C_cyclotomic_dvd_iff_map_zero hn hz _).mpr
    dsimp only [ua, ub]
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_deletedBoundary,
      map_boundaryDA, map_boundaryDB, map_pow, map_neg, map_one]
    rw [show (aeval z).toRingHom (X : ℚ[X]) = z from aeval_X z]
    exact deleted_match hz hn h4
  have hc : C (cyclotomic n ℚ) ∣ C (1-(X : ℚ[X])^n) := map_dvd C hfirst
  have he := mul_dvd_mul hc hsecond
  rw [hna, hnb, C_pow, pow_two]
  rw [mul_assoc, mul_assoc, ← mul_sub]
  exact he

#print axioms boundary_cross_sq
end
end GuoWang.Clear
```

### `GWBoundaryRegular.lean`

```lean
import GWBoundaryMatch

namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K} {n : ℕ}

lemma boundaryBase_root_ne (hz : IsPrimitiveRoot z n) (hn : 1 < n) (hc : n.Coprime 4) :
    boundaryBase z n ≠ 0 := by
  unfold boundaryBase
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact C_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm (hz.ne_one hn)))
    · apply Finset.prod_ne_zero_iff.mpr
      intro j _ he
      have he' := congrArg (fun p : K[X] => p.eval 0) he
      simp at he'
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply mul_ne_zero (monic_X_sub_C _).ne_zero
    apply C_ne_zero.mpr
    intro he
    have hd := (hz.pow_eq_one_iff_dvd (4+4*j)).mp (sub_eq_zero.mp he).symm
    have hd' : n ∣ 4*(j+1) := by convert hd using 1; omega
    have hj' := hc.dvd_mul_left.mp hd'
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by have := Finset.mem_range.mp hj; omega)) hj'

lemma boundaryDA_root_ne (hz : IsPrimitiveRoot z n) (hn : 1 < n) (hc : n.Coprime 4) :
    boundaryDA z n ≠ 0 := by
  have h2 : z^(2*n) = 1 := by rw [mul_comm 2 n, pow_mul, hz.pow_eq_one, one_pow]
  unfold boundaryDA
  rw [h2]
  apply mul_ne_zero (mul_ne_zero (boundaryBase_root_ne hz hn hc) ?_) ?_ <;>
    intro he <;>
    have he' := congrArg (fun p : K[X] => p.eval 0) he <;>
    simp at he'

lemma boundaryDB_root_ne (hz : IsPrimitiveRoot z n) (hn : 1 < n) (hc : n.Coprime 4) :
    boundaryDB z n ≠ 0 := by
  have h4' : z^(4*n) = 1 := by rw [mul_comm 4 n, pow_mul, hz.pow_eq_one, one_pow]
  unfold boundaryDB
  rw [h4']
  apply mul_ne_zero (mul_ne_zero (boundaryBase_root_ne hz hn hc) ?_) ?_ <;>
    intro he <;>
    have he' := congrArg (fun p : K[X] => p.eval 0) he <;>
    simp at he'

/-- Cancellation is prime-factor cancellation in ℚ[q][a], not a false
Bezout-coprimality assertion about two-variable polynomials. -/
theorem actual_operator_sq (hz : IsPrimitiveRoot z n) (hn : 1 < n) (h4 : n % 4 = 1) :
    C ((cyclotomic n ℚ)^2) ∣ shiftOperator ((X : ℚ[X])^4) (P n) (H n) := by
  have hp : Prime (C (cyclotomic n ℚ) : Polynomial ℚ[X]) :=
    Polynomial.prime_C_iff.mpr (cyclotomic.irreducible_rat (by omega)).prime
  have hna : ¬ C (cyclotomic n ℚ) ∣ boundaryDA (X : ℚ[X]) n := by
    intro he
    have hh := (C_cyclotomic_dvd_iff_map_zero (by omega) hz _).mp he
    rw [map_boundaryDA, show (aeval z).toRingHom (X : ℚ[X]) = z from aeval_X z] at hh
    exact boundaryDA_root_ne hz hn (coprime_four h4) hh
  have hnb : ¬ C (cyclotomic n ℚ) ∣ boundaryDB (X : ℚ[X]) n := by
    intro he
    have hh := (C_cyclotomic_dvd_iff_map_zero (by omega) hz _).mp he
    rw [map_boundaryDB, show (aeval z).toRingHom (X : ℚ[X]) = z from aeval_X z] at hh
    exact boundaryDB_root_ne hz hn (coprime_four h4) hh
  have he := dvd_mul_of_dvd_right (boundary_cross_sq hz (by omega) h4)
    (H n * rescale ((X : ℚ[X])^4) (H n))
  rw [← polynomial_recurrence n (by omega), C_pow] at he
  have hcancel := hp.pow_dvd_of_dvd_mul_right 2 hnb he
  rw [← C_pow] at hcancel
  have hcancel' : C (cyclotomic n ℚ)^2 ∣
      shiftOperator ((X : ℚ[X])^4) (P n) (H n) * boundaryDA (X : ℚ[X]) n := by
    simpa only [C_pow] using hcancel
  simpa only [C_pow] using hp.pow_dvd_of_dvd_mul_right 2 hna hcancel'

#print axioms actual_operator_sq
end
end GuoWang.Clear
```

### `GWTopFourth.lean`

```lean
import GWBoundaryRegular
import GWTerminatingRoots
import GWExtractFourth

namespace GuoWang
open Polynomial
noncomputable section

/-- The fourth top cyclotomic factor, with no intermediate mathematical input. -/
theorem top_fourth (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    (cyclotomic n ℚ)^4 ∣ (diff n).num := by
  by_cases he : n = 1
  · subst n
    simp only [diff_one, RatFunc.num_zero]
    exact dvd_zero _
  · have hn' : 1 < n := by omega
    let z := Complex.exp (2*Real.pi*Complex.I/n)
    have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
    exact Clear.top_fourth_of_parameter_roots n hn h4 z hz
      (Clear.P_sq_dvd_of_operator hn hz h4 (Clear.actual_operator_sq hz hn' h4))
      (Clear.at_P_qn n hn h4) (Clear.at_P_qn_inverse n hn h4)

#print axioms top_fourth
end
end GuoWang
```

### `GWValues.lean`

```lean
import GWClearRoots

/-! Faithful value witnesses, the value-only version of the sibling's fraction
and jet interface. Singular factors must be cancelled before this interface
can be used. -/
namespace GuoWang
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
abbrev embed : ℚ[X] →+* RatFunc ℚ := algebraMap _ _

def HasValue (z : K) (f : RatFunc ℚ) (v : K) : Prop :=
  ∃ A B : ℚ[X], aeval z B ≠ 0 ∧ f = embed A / embed B ∧
    aeval z A / aeval z B = v

namespace HasValue
variable {z : K} {f g : RatFunc ℚ} {v w : K}

lemma poly (A : ℚ[X]) : HasValue z (embed A) (aeval z A) := by
  exact ⟨A, 1, by simp, by simp, by simp⟩
lemma zero : HasValue z 0 0 := by simpa using (poly (z := z) 0)
lemma one : HasValue z 1 1 := by simpa using (poly (z := z) 1)
lemma const (c : ℚ) : HasValue z (algebraMap ℚ (RatFunc ℚ) c) (algebraMap ℚ K c) := by
  simpa using (poly (z := z) (C c))
lemma qpow (k : ℕ) : HasValue z (X'^k) (z^k) := by
  simpa only [map_pow, RatFunc.algebraMap_X, aeval_X, X'] using (poly (z := z) (X^k))

lemma mul (hf : HasValue z f v) (hg : HasValue z g w) : HasValue z (f*g) (v*w) := by
  obtain ⟨A,B,hB,rfl,hv⟩ := hf
  obtain ⟨C,D,hD,rfl,hw⟩ := hg
  refine ⟨A*C,B*D,by simpa using mul_ne_zero hB hD,?_,?_⟩
  · simp only [map_mul]; exact div_mul_div_comm _ _ _ _
  · simp only [map_mul, ← hv, ← hw]; exact (div_mul_div_comm _ _ _ _).symm

lemma add (hf : HasValue z f v) (hg : HasValue z g w) : HasValue z (f+g) (v+w) := by
  obtain ⟨A,B,hB,rfl,hv⟩ := hf
  obtain ⟨C,D,hD,rfl,hw⟩ := hg
  have hB' : B ≠ 0 := by intro he; exact hB (by rw [he,map_zero])
  have hD' : D ≠ 0 := by intro he; exact hD (by rw [he,map_zero])
  refine ⟨A*D+C*B,B*D,by simpa using mul_ne_zero hB hD,?_,?_⟩
  · simp only [map_mul, map_add]
    simpa only [mul_comm (embed C) (embed B)] using
      div_add_div (embed A) (embed C) (RatFunc.algebraMap_ne_zero hB') (RatFunc.algebraMap_ne_zero hD')
  · simp only [map_mul, map_add, ← hv, ← hw]
    simpa only [mul_comm (aeval z C) (aeval z B)] using
      (div_add_div (aeval z A) (aeval z C) hB hD).symm

lemma neg (hf : HasValue z f v) : HasValue z (-f) (-v) := by
  obtain ⟨A,B,hB,rfl,hv⟩ := hf
  exact ⟨-A,B,hB,by simp only [map_neg, neg_div],by simp only [map_neg, neg_div, hv]⟩
lemma sub (hf : HasValue z f v) (hg : HasValue z g w) : HasValue z (f-g) (v-w) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma pow (hf : HasValue z f v) (k : ℕ) : HasValue z (f^k) (v^k) := by
  induction k with
  | zero => simpa using (one (z := z))
  | succ k ih => simpa only [pow_succ] using ih.mul hf

lemma div (hf : HasValue z f v) (hg : HasValue z g w) (hw : w ≠ 0) : HasValue z (f/g) (v/w) := by
  obtain ⟨A,B,hB,rfl,hv⟩ := hf
  obtain ⟨C,D,hD,rfl,hval⟩ := hg
  have hC : aeval z C ≠ 0 := by intro he; apply hw; rw [← hval,he,zero_div]
  refine ⟨A*D,B*C,by simpa using mul_ne_zero hB hC,?_,?_⟩
  · simp only [map_mul]; rw [div_div_div_eq]
  · simp only [map_mul, ← hv, ← hval]; rw [div_div_div_eq]

lemma sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) (v : ι → K)
    (h : ∀ i ∈ s, HasValue z (f i) (v i)) : HasValue z (∑ i ∈ s, f i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (z := z))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma prod {ι : Type*} (s : Finset ι) (f : ι → RatFunc ℚ) (v : ι → K)
    (h : ∀ i ∈ s, HasValue z (f i) (v i)) : HasValue z (∏ i ∈ s, f i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (z := z))
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma numerator_root (hf : HasValue z f 0) : aeval z f.num = 0 := by
  obtain ⟨A,B,hB,hf,hv⟩ := hf
  have hB' : B ≠ 0 := by intro he; exact hB (by rw [he,map_zero])
  have hc := (RatFunc.num_mul_eq_mul_denom_iff hB').mpr hf
  have hc' := congrArg (aeval z) hc
  have hA := (div_eq_zero_iff.mp hv).resolve_right hB
  simp only [map_mul, hA, zero_mul] at hc'
  exact (mul_eq_zero.mp hc').resolve_right hB

lemma cyclotomic_dvd_num {n : ℕ} (hn : 0 < n) (hz : IsPrimitiveRoot z n)
    (hf : HasValue z f 0) : cyclotomic n ℚ ∣ f.num :=
  (Clear.cyclotomic_dvd_iff_root hn hz _).mpr hf.numerator_root
end HasValue
end
end GuoWang
```

### `GWBlockPolynomials.lean`

```lean
import GWValues
import GWResidueProducts
import Mathlib.Algebra.Polynomial.BigOperators

/-! Zero-factor cancellation in a complete block, adapted from the sibling's
geometric block representatives and generalized to numerator strides 2 and 4. -/
namespace GuoWang.Block
open Polynomial
noncomputable section

def pochPoly (t s k : ℕ) : ℚ[X] := ∏ j ∈ Finset.range k, (1-X^(t+s*j))
def geom (d a : ℕ) : ℚ[X] := ∑ j ∈ Finset.range a, X^(d*j)
def bn (d s h t l : ℕ) : ℚ[X] :=
  geom d (s*l+t) * ∏ j ∈ (Finset.range d).erase h, (1-X^(s*l*d+1+s*j))
def bd (d l : ℕ) : ℚ[X] :=
  geom d (4*l+4) * ∏ j ∈ (Finset.range d).erase (d-1), (1-X^(4*l*d+4+4*j))

lemma pochPoly_map (t s k : ℕ) : embed (pochPoly t s k) = poch (X'^t) (X'^s) k := by
  simp only [pochPoly, poch, map_prod, map_sub, map_one, map_pow, RatFunc.algebraMap_X]
  apply Finset.prod_congr rfl
  intro j _
  rw [← pow_mul, ← pow_add]
  rfl

lemma geom_map (d a : ℕ) : embed (geom d a) = ∑ j ∈ Finset.range a, X'^(d*j) := by
  simp [geom, X']

lemma geometric_cancel {K : Type*} [Field K] (x : K) (a b : ℕ) (hx : x ≠ 1) :
    (1-x^a)/(1-x^b) = (∑ j ∈ Finset.range a, x^j)/(∑ j ∈ Finset.range b, x^j) := by
  have he (k : ℕ) : 1-x^k = (∑ j ∈ Finset.range k, x^j)*(1-x) :=
    (geom_sum_mul_neg x k).symm
  rw [he a, he b, mul_div_mul_right]
  exact sub_ne_zero.mpr (Ne.symm hx)

lemma zero_factor_cancel (d a b : ℕ) (hd : 0 < d) :
    (1-X'^(d*a))/(1-X'^(d*b)) = embed (geom d a)/embed (geom d b) := by
  rw [geom_map,geom_map]
  simp_rw [pow_mul]
  exact geometric_cancel (X'^d) a b (GuoWang.X'_pow_ne_one d hd)

/-- Equality of actual rational functions, before root evaluation. -/
theorem block_fraction (d s h t l : ℕ) (hd : 0 < d) (hh : h < d) (ht : 1+s*h=t*d) :
    poch (X'^(s*l*d+1)) (X'^s) d / poch (X'^(4*l*d+4)) (X'^4) d =
      embed (bn d s h t l)/embed (bd d l) := by
  have hn := Finset.mul_prod_erase (Finset.range d)
    (fun j => 1-X'^(s*l*d+1+s*j)) (Finset.mem_range.mpr hh)
  have hD := Finset.mul_prod_erase (Finset.range d)
    (fun j => 1-X'^(4*l*d+4+4*j)) (Finset.mem_range.mpr (show d-1 < d by omega))
  have heN : s*l*d+1+s*h = d*(s*l+t) := by rw [add_assoc,ht]; ring
  have heD : 4*l*d+4+4*(d-1) = d*(4*l+4) := by
    calc
      _ = 4*l*d+4*d := by omega
      _ = _ := by ring
  simp only [poch, ← pow_mul, ← pow_add]
  rw [← hn,← hD,heN,heD]
  rw [mul_div_mul_comm, zero_factor_cancel d _ _ hd]
  simp only [bn,bd,map_mul,map_prod,map_sub,map_one,map_pow,RatFunc.algebraMap_X]
  rw [mul_div_mul_comm]
  rfl

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K} {d : ℕ}

lemma geom_root (a : ℕ) (hz : z^d=1) : aeval z (geom d a) = (a:K) := by
  simp [geom,pow_mul,hz]

omit [CharZero K] in
lemma shifted_power (s l a : ℕ) (hz : z^d=1) : z^(s*l*d+a)=z^a := by
  rw [pow_add,show s*l*d=d*(s*l) by ring,pow_mul,hz,one_pow,one_mul]

lemma bn_root (hz : IsPrimitiveRoot z d) (hd : 0 < d) (s h t l : ℕ)
    (hs : d.Coprime s) (hh : h < d) (ht : 1+s*h=t*d) :
    aeval z (bn d s h t l) = (s*l+t:ℕ)*(d:K) := by
  have hzero : z^(1+s*h)=1 := by rw [ht,mul_comm t d,pow_mul,hz.pow_eq_one,one_pow]
  simp only [bn,map_mul,geom_root _ hz.pow_eq_one,map_prod,map_sub,map_one,map_pow,aeval_X]
  simp_rw [show ∀ j, s*l*d+1+s*j=s*l*d+(1+s*j) from fun j => by omega,
    shifted_power s l _ hz.pow_eq_one]
  rw [GuoWang.Residues.deleted_product hz hd s hs h hh hzero]

lemma bd_root (hz : IsPrimitiveRoot z d) (hd : 0 < d) (hc : d.Coprime 4) (l : ℕ) :
    aeval z (bd d l) = (4*l+4:ℕ)*(d:K) := by
  have hz4 := hz.pow_of_coprime 4 hc.symm
  have hzero : (z^4)^(1+1*(d-1))=1 := by
    rw [show 1+1*(d-1)=d by omega,hz4.pow_eq_one]
  simp only [bd,map_mul,geom_root _ hz.pow_eq_one,map_prod,map_sub,map_one,map_pow,aeval_X]
  simp_rw [show ∀ j, 4*l*d+4+4*j=4*l*d+(4+4*j) from fun j => by omega,
    shifted_power 4 l _ hz.pow_eq_one]
  have he := GuoWang.Residues.deleted_product hz4 hd 1 (Nat.coprime_one_right d)
    (d-1) (by omega) hzero
  have hp : (∏ j ∈ (Finset.range d).erase (d-1), (1-z^(4+4*j))) = (d:K) := by
    convert he using 1
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul]
    congr 2
    omega
  rw [hp]

/-- A cancelled block is regular, with its exact rational multiplier. -/
theorem block_value (hz : IsPrimitiveRoot z d) (hd : 0 < d) (hc : d.Coprime 4)
    (s h t l : ℕ) (hs : d.Coprime s) (hh : h < d) (ht : 1+s*h=t*d) :
    HasValue z (poch (X'^(s*l*d+1)) (X'^s) d / poch (X'^(4*l*d+4)) (X'^4) d)
      ((s*l+t:ℕ)/(4*l+4:ℕ):K) := by
  refine ⟨bn d s h t l,bd d l,?_,block_fraction d s h t l hd hh ht,?_⟩
  · rw [bd_root hz hd hc]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr hd.ne')
  · rw [bn_root hz hd s h t l hs hh ht,bd_root hz hd hc]
    exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hd.ne')
end Roots
end
end GuoWang.Block
```

### `GWFamilyPolynomials.lean`

```lean
import GWPolynomialRecurrence

namespace GuoWang.Clear
open Polynomial GuoWang.WZ
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

def familyNum (q : R) (b : Bool) (k : ℕ) : R[X] :=
  if b then num q 2 6 (3*k^2) k else num q 4 8 (2*k^2+k) k

def familyPoly (q : R) (b : Bool) (N : ℕ) : R[X] :=
  ∑ k ∈ Finset.range N, familyNum q b k * complement q N k

def familyBN (q : R) (b : Bool) (N : ℕ) : R[X] :=
  if b then boundaryNA q N else boundaryNB q N

def familyBD (q : R) (b : Bool) (N : ℕ) : R[X] :=
  if b then boundaryDA q N else boundaryDB q N

@[simp] lemma map_familyPoly (f : R →+* S) (q : R) (b : Bool) (N : ℕ) :
    (familyPoly q b N).map f = familyPoly (f q) b N := by
  cases b <;> simp [familyPoly,familyNum,Polynomial.map_sum]
@[simp] lemma map_familyBN (f : R →+* S) (q : R) (b : Bool) (N : ℕ) :
    (familyBN q b N).map f = familyBN (f q) b N := by cases b <;> simp [familyBN]
@[simp] lemma map_familyBD (f : R →+* S) (q : R) (b : Bool) (N : ℕ) :
    (familyBD q b N).map f = familyBD (f q) b N := by cases b <;> simp [familyBD]

section Field
variable {K : Type*} [Field K]

def familySum (q a : K) (b : Bool) (N : ℕ) : K :=
  ∑ k ∈ Finset.range N, if b then fa q a k else fb q a k

lemma family_fraction (q a : K) (b : Bool) (N : ℕ) (ha : a ≠ 0)
    (hd : ∀ k < N, (den q k).eval a ≠ 0) :
    familySum q a b N = (familyPoly q b N).eval a / (commonDen q N).eval a := by
  have hC : (commonDen q N).eval a ≠ 0 := by
    simp only [commonDen, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k hk => hd k (Finset.mem_range.mp hk))
  unfold familySum
  have hf (k : ℕ) : (if b then fa q a k else fb q a k) =
      (familyNum q b k).eval a / (den q k).eval a := by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, familyNum, fa, fb,
      ft_eq_term q a _ _ _ _ ha, term]
  simp_rw [hf]
  simp only [familyPoly, eval_finsetSum, eval_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have he := congrArg (fun p : K[X] => p.eval a)
    (den_mul_complement q N k (Finset.mem_range.mp hk))
  rw [eval_mul] at he
  apply (eq_div_iff hC).mpr
  rw [← he]
  field_simp [hd k (Finset.mem_range.mp hk)]

lemma family_recurrence_value (q a : K) (h : Good q a) (b : Bool) (N : ℕ) (hN : 0 < N) :
    (shiftOperator (q^4) (familyPoly q b N) (commonDen q N)).eval a * (familyBD q b N).eval a =
      (commonDen q N).eval a * (commonDen q N).eval (a*q^4) * (familyBN q b N).eval a := by
  have he : (1-a⁻¹)*familySum q (a*q^4) b N-(1-a*q^4)*familySum q a b N =
      if b then ca q a N else cb q a N := by
    cases b
    · simp only [familySum, Bool.false_eq_true, ite_false]
      rw [← gb_cancelled q a h N hN]
      exact finite_shift_recurrence _ _ _ _ _ N (fun k _ => fb_step q a h k) (gb_zero q a)
    · simp only [familySum, ite_true]
      rw [← ga_cancelled q a h N hN]
      exact finite_shift_recurrence _ _ _ _ _ N (fun k _ => fa_step q a h k) (ga_zero q a)
  rw [family_fraction q _ b N h.shift.a_ne (fun k _ => h.shift.den_ne k),
    family_fraction q a b N h.a_ne (fun k _ => h.den_ne k)] at he
  have hb : (familyBD q b N).eval a ≠ 0 := by
    cases b <;> simp only [familyBD, Bool.false_eq_true, ite_false, ite_true]
    · exact boundaryDB_good q a h N
    · exact boundaryDA_good q a h N
  have hr : (if b then ca q a N else cb q a N) =
      (familyBN q b N).eval a / (a*(familyBD q b N).eval a) := by
    cases b <;> simp only [familyBN,familyBD,Bool.false_eq_true,ite_false,ite_true]
    · exact cb_fraction q a N hN h.a_ne
    · exact ca_fraction q a N hN h.a_ne
  rw [hr] at he
  have hd : (commonDen q N).eval a ≠ 0 := by
    simp only [commonDen,eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => h.den_ne k)
  have hs : (commonDen q N).eval (a*q^4) ≠ 0 := by
    simp only [commonDen,eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => h.shift.den_ne k)
  simp only [shiftOperator,eval_sub,eval_mul,eval_X,eval_one,eval_C,eval_rescale]
  field_simp [h.a_ne,hd,hs,hb] at he
  linear_combination he
end Field

theorem family_polynomial_recurrence (b : Bool) (N : ℕ) (hN : 0 < N) :
    shiftOperator ((X : ℚ[X])^4) (familyPoly (X : ℚ[X]) b N) (H N) * familyBD (X : ℚ[X]) b N =
      H N * rescale ((X : ℚ[X])^4) (H N) * familyBN (X : ℚ[X]) b N := by
  apply Polynomial.map_injective qMap (RatFunc.algebraMap_injective ℚ)
  apply RatFunc.algebraMap_injective F
  rw [← eval_generic,← eval_generic]
  have he := family_recurrence_value genericQ genericA generic_good b N hN
  simpa only [Polynomial.map_mul, map_shiftOperator, H, map_commonDen, map_familyPoly,
    map_familyBD, map_familyBN, map_rescale, map_pow, RatFunc.algebraMap_X, eval_mul,
    eval_rescale, genericQ, GuoWang.X'] using he

#print axioms family_polynomial_recurrence
end
end GuoWang.Clear
```

### `GWFamilyRoots.lean`

```lean
import GWFamilyPolynomials
import GWBoundaryRegular
import GWValues

namespace GuoWang.Clear
open Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {z : K} {d : ℕ}

lemma odd_coprime_four (ho : Odd d) : d.Coprime 4 := by
  simpa using ho.coprime_two_right.pow_right 2

lemma den_root_general (hz : IsPrimitiveRoot z d) (hc : d.Coprime 4) (k : ℕ) (hk : k < d) :
    den z k ≠ 0 ∧ (den z k).eval 1 ≠ 0 := by
  have hfactor (j : ℕ) (hj : j < k) : 1-z^(4+4*j) ≠ 0 := by
    intro he
    have hd := (hz.pow_eq_one_iff_dvd (4+4*j)).mp (sub_eq_zero.mp he).symm
    have hd' : d ∣ 4*(j+1) := by convert hd using 1; omega
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) (hc.dvd_mul_left.mp hd')
  constructor
  · unfold den pairPoch
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hlin : (1-X*C (z^(4+4*j)) : K[X]) ≠ 0 := by
      intro he
      have hh := congrArg (fun p : K[X] => p.eval 0) he
      simp at hh
    exact mul_ne_zero (mul_ne_zero hlin (monic_X_sub_C _).ne_zero)
      (C_ne_zero.mpr (hfactor j (Finset.mem_range.mp hj)))
  · simp only [den,eval_pairPoch,one_mul]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact mul_ne_zero (mul_ne_zero (hfactor j (Finset.mem_range.mp hj))
      (hfactor j (Finset.mem_range.mp hj))) (hfactor j (Finset.mem_range.mp hj))

lemma H_root_general (hz : IsPrimitiveRoot z d) (hc : d.Coprime 4) :
    (H d).map (aeval z).toRingHom ≠ 0 ∧ ((H d).map (aeval z).toRingHom).eval 1 ≠ 0 := by
  rw [H,map_commonDen,show (aeval z).toRingHom (X : ℚ[X]) = z from aeval_X z]
  constructor
  · unfold commonDen
    exact Finset.prod_ne_zero_iff.mpr (fun k hk => (den_root_general hz hc k (Finset.mem_range.mp hk)).1)
  · simp only [commonDen,eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k hk => (den_root_general hz hc k (Finset.mem_range.mp hk)).2)

omit [CharZero K] in
lemma pairPoch_root_zero (hz : IsPrimitiveRoot z d) (s : ℕ)
    (hj : ∃ j < d, d ∣ 1+s*j) : pairPoch z 1 s d = 0 := by
  obtain ⟨j,hj,hdj⟩ := hj
  unfold pairPoch
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
  rw [(hz.pow_eq_one_iff_dvd _).mpr hdj,sub_self,C_0,mul_zero]

lemma odd_zero_indices (ho : Odd d) (hd : 0 < d) :
    (∃ j < d, d ∣ 1+2*j) ∧ (∃ j < d, d ∣ 1+4*j) := by
  obtain ⟨m,hm⟩ := ho
  constructor
  · refine ⟨m,by omega,?_⟩
    have he : 1+2*m=d := by omega
    rw [he]
  · by_cases h4 : d%4=1
    · refine ⟨(d-1)/4,by omega,?_⟩
      have he : 1+4*((d-1)/4)=d := by omega
      rw [he]
    · have h4' : d%4=3 := by omega
      refine ⟨(3*d-1)/4,by omega,?_⟩
      have he : 1+4*((3*d-1)/4)=3*d := by omega
      rw [he]
      exact dvd_mul_left d 3

/-- The individual short sums vanish for every odd order, including 3 mod 4. -/
theorem family_poly_root_zero (hz : IsPrimitiveRoot z d) (hd : 1 < d) (ho : Odd d) (b : Bool) :
    (familyPoly (X : ℚ[X]) b d).map (aeval z).toRingHom = 0 := by
  have hc := odd_coprime_four ho
  have hBN : familyBN z b d = 0 := by
    obtain ⟨hA,hB⟩ := odd_zero_indices ho (by omega)
    cases b <;> simp only [familyBN,boundaryNA,boundaryNB,boundaryNum,
      Bool.false_eq_true,ite_false,ite_true]
    · rw [pairPoch_root_zero hz 4 hB,mul_zero]
    · rw [pairPoch_root_zero hz 2 hA,mul_zero]
  have hBD : familyBD z b d ≠ 0 := by
    cases b <;> simp only [familyBD,Bool.false_eq_true,ite_false,ite_true]
    · exact boundaryDB_root_ne hz hd hc
    · exact boundaryDA_root_ne hz hd hc
  have he := congrArg (fun p : Polynomial ℚ[X] => p.map (aeval z).toRingHom)
    (family_polynomial_recurrence b d (by omega))
  simp only [Polynomial.map_mul,map_shiftOperator,map_familyBD,map_familyBN,map_pow] at he
  rw [show (aeval z).toRingHom (X : ℚ[X]) = z from aeval_X z,hBN,mul_zero] at he
  have hop := (mul_eq_zero.mp he).resolve_right hBD
  apply homogeneous_shift_zero (z^4) (pow_ne_zero 4 (hz.ne_zero (by omega))) _ _
    (H_root_general hz hc).1
  exact sub_eq_zero.mp hop

#print axioms family_poly_root_zero
end
end GuoWang.Clear
```

### `GWLongRatio.lean`

```lean
import GWBlockPolynomials

namespace GuoWang.Block
open Polynomial
noncomputable section

lemma poch_add (a s k l : ℕ) :
    poch (X'^a) (X'^s) (k+l) = poch (X'^a) (X'^s) k * poch (X'^(a+s*k)) (X'^s) l := by
  simp only [poch,Finset.prod_range_add,← pow_mul,← pow_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  ring

lemma poch_blocks (a s d l : ℕ) :
    poch (X'^a) (X'^s) (l*d) = ∏ u ∈ Finset.range l, poch (X'^(a+s*(u*d))) (X'^s) d := by
  induction l with
  | zero => simp [poch]
  | succ l ih => rw [Nat.succ_mul,poch_add,ih,Finset.prod_range_succ]

def ratio (s k : ℕ) : RatFunc ℚ := poch X' (X'^s) k / poch (X'^4) (X'^4) k

def shortRatio {K : Type*} [Field K] (z : K) (s k : ℕ) : K :=
  QWZCore.poch z (z^s) k / QWZCore.poch (z^4) (z^4) k

def coefficient {K : Type*} [Field K] (s t l : ℕ) : K :=
  ∏ u ∈ Finset.range l, ((s*u+t:ℕ)/(4*u+4:ℕ):K)

lemma ratio_blocks (s d l r : ℕ) :
    ratio s (l*d+r) =
      (∏ u ∈ Finset.range l,
        poch (X'^(s*u*d+1)) (X'^s) d / poch (X'^(4*u*d+4)) (X'^4) d) *
      (poch (X'^(s*l*d+1)) (X'^s) r / poch (X'^(4*l*d+4)) (X'^4) r) := by
  unfold ratio
  nth_rw 1 [show X' = X'^1 by simp]
  rw [poch_add,poch_add,poch_blocks,poch_blocks,Finset.prod_div_distrib]
  simp only [show ∀ u, 1+s*(u*d)=s*u*d+1 from fun u => by ring,
    show ∀ u, 4+4*(u*d)=4*u*d+4 from fun u => by ring]
  exact mul_div_mul_comm _ _ _ _

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K} {d : ℕ}

lemma pochPoly_root (t s k : ℕ) :
    aeval z (pochPoly t s k) = QWZCore.poch (z^t) (z^s) k := by
  simp only [pochPoly,map_prod,map_sub,map_one,map_pow,aeval_X,QWZCore.poch,
    ← pow_mul,← pow_add]

omit [CharZero K] in
lemma short_den_ne (hz : IsPrimitiveRoot z d) (hc : d.Coprime 4) (r : ℕ) (hr : r < d) :
    QWZCore.poch (z^4) (z^4) r ≠ 0 := by
  unfold QWZCore.poch
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [← pow_mul,← pow_add]
  intro he
  have hh := (hz.pow_eq_one_iff_dvd (4+4*j)).mp (sub_eq_zero.mp he).symm
  have hh' : d ∣ 4*(j+1) := by convert hh using 1; omega
  exact (Nat.not_dvd_of_pos_of_lt (by omega) (by have := Finset.mem_range.mp hj; omega))
    (hc.dvd_mul_left.mp hh')

lemma suffix_value (hz : IsPrimitiveRoot z d) (hc : d.Coprime 4) (s l r : ℕ) (hr : r < d) :
    HasValue z (poch (X'^(s*l*d+1)) (X'^s) r / poch (X'^(4*l*d+4)) (X'^4) r)
      (shortRatio z s r) := by
  have hp (a t k : ℕ) := HasValue.poly (z := z) (pochPoly a t k)
  have hn := hp (s*l*d+1) s r
  have hd := hp (4*l*d+4) 4 r
  simp only [pochPoly_map,pochPoly_root,shifted_power s l 1 hz.pow_eq_one,
    shifted_power 4 l 4 hz.pow_eq_one,pow_one] at hn hd
  exact hn.div hd (short_den_ne hz hc r hr)

/-- The whole long quotient, including zero tails, is represented regularly. -/
theorem ratio_value (hz : IsPrimitiveRoot z d) (hd : 0 < d) (hc : d.Coprime 4)
    (s h t l r : ℕ) (hs : d.Coprime s) (hh : h < d) (ht : 1+s*h=t*d) (hr : r < d) :
    HasValue z (ratio s (l*d+r)) (coefficient (K := K) s t l * shortRatio z s r) := by
  rw [ratio_blocks]
  exact (HasValue.prod (Finset.range l) _ _
    (fun u _ => block_value hz hd hc s h t u hs hh ht)).mul (suffix_value hz hc s l r hr)

end Roots
end
end GuoWang.Block
```

### `GWBlockTerms.lean`

```lean
import GWLongRatio
import GWFamilyRoots

namespace GuoWang.Block
open Polynomial
noncomputable section

def stride (b : Bool) : ℕ := if b then 2 else 4
def weight (b : Bool) : ℕ := if b then 6 else 8
def exponent (b : Bool) (k : ℕ) : ℕ := if b then 3*k^2 else 2*k^2+k

def source (b : Bool) (k : ℕ) : RatFunc ℚ := if b then L k else R k

def fieldSource {K : Type*} [Field K] (z : K) (b : Bool) (k : ℕ) : K :=
  if b then GuoWang.WZ.fa z 1 k else GuoWang.WZ.fb z 1 k

lemma source_repr (b : Bool) (k : ℕ) : source b k =
    (-1)^k * qInt (weight b*k+1) * X'^(exponent b k) * (ratio (stride b) k)^3 := by
  cases b <;> simp only [source,weight,stride,exponent,Bool.false_eq_true,ite_false,ite_true,
    L,R,ratio,div_pow] <;> ring

lemma fieldSource_repr {K : Type*} [Field K] (z : K) (b : Bool) (k : ℕ) : fieldSource z b k =
    (-1)^k * (∑ j ∈ Finset.range (weight b*k+1), z^j) * z^(exponent b k) *
      (shortRatio z (stride b) k)^3 := by
  cases b <;> simp only [fieldSource,weight,stride,exponent,Bool.false_eq_true,ite_false,ite_true,
    GuoWang.WZ.fa,GuoWang.WZ.fb,GuoWang.WZ.ft,GuoWang.WZ.pd,GuoWang.WZ.pair,
    one_mul,div_one,pow_one,shortRatio,div_pow] <;> ring

section Roots
variable {K : Type*} [Field K] [CharZero K] {z : K} {d : ℕ}

lemma source_value_of_ratio (b : Bool) (k : ℕ) (v : K) (hv : HasValue z (ratio (stride b) k) v) :
    HasValue z (source b k)
      ((-1:K)^k * (∑ j ∈ Finset.range (weight b*k+1), z^j) * z^(exponent b k) * v^3) := by
  have hq := HasValue.poly (z := z) (qIntPoly (weight b*k+1))
  simp only [qIntPoly,map_sum,map_pow,aeval_X] at hq
  have hq' : HasValue z (qInt (weight b*k+1)) (∑ j ∈ Finset.range (weight b*k+1), z^j) := by
    simpa only [qInt_eq_sum,RatFunc.algebraMap_X,X'] using hq
  have h := (((HasValue.const (z := z) (-1)).pow k).mul hq').mul
    (HasValue.qpow (z := z) (exponent b k))
  rw [source_repr]
  simpa only [map_neg,map_one] using h.mul (hv.pow 3)

omit [CharZero K] in
lemma qInt_periodic (hz : IsPrimitiveRoot z d) (hd : 1 < d) (w l r : ℕ) :
    (∑ j ∈ Finset.range (w*(l*d+r)+1), z^j) = ∑ j ∈ Finset.range (w*r+1), z^j := by
  have hq : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz.ne_one hd))
  apply mul_right_cancel₀ hq
  rw [geom_sum_mul_neg,geom_sum_mul_neg]
  congr 1
  rw [show w*(l*d+r)+1 = d*(w*l)+(w*r+1) by ring,pow_add,pow_mul,hz.pow_eq_one,one_pow,one_mul]

omit [CharZero K] in
lemma exponent_periodic (hz : IsPrimitiveRoot z d) (b : Bool) (l r : ℕ) :
    z^(exponent b (l*d+r)) = z^(exponent b r) := by
  cases b
  · simp only [exponent,Bool.false_eq_true,ite_false]
    rw [show 2*(l*d+r)^2+(l*d+r) = d*(2*l^2*d+4*l*r+l)+(2*r^2+r) by ring,
      pow_add,pow_mul,hz.pow_eq_one,one_pow,one_mul]
  · simp only [exponent,ite_true]
    rw [show 3*(l*d+r)^2 = d*(3*l^2*d+6*l*r)+3*r^2 by ring,
      pow_add,pow_mul,hz.pow_eq_one,one_pow,one_mul]

omit [CharZero K] in
lemma sign_periodic (ho : Odd d) (l r : ℕ) :
    (-1:K)^(l*d+r) = (-1:K)^l*(-1:K)^r := by
  rw [pow_add,Nat.mul_comm l d,pow_mul,ho.neg_one_pow]

/-- Each full block is an exact scalar multiple of its short source block. -/
theorem source_block_value (hz : IsPrimitiveRoot z d) (hd : 1 < d) (ho : Odd d)
    (b : Bool) (h t l r : ℕ) (hs : d.Coprime (stride b))
    (hh : h < d) (ht : 1+stride b*h=t*d) (hr : r < d) :
    HasValue z (source b (l*d+r))
      (((-1:K)^l * (coefficient (K := K) (stride b) t l)^3) * fieldSource z b r) := by
  have hv := ratio_value hz (by omega) (Clear.odd_coprime_four ho)
    (stride b) h t l r hs hh ht hr
  have hv' := source_value_of_ratio b (l*d+r) _ hv
  rw [qInt_periodic hz hd,exponent_periodic hz,sign_periodic ho] at hv'
  rw [fieldSource_repr]
  convert hv' using 1
  ring

lemma family_sum_root (hz : IsPrimitiveRoot z d) (hd : 1 < d) (ho : Odd d) (b : Bool) :
    (∑ r ∈ Finset.range d, fieldSource z b r) = 0 := by
  have hp := Clear.family_poly_root_zero hz hd ho b
  rw [Clear.map_familyPoly,show (aeval z).toRingHom (X : ℚ[X]) = z from aeval_X z] at hp
  change Clear.familySum z 1 b d = 0
  rw [Clear.family_fraction z 1 b d one_ne_zero (fun k hk =>
    (Clear.den_root_general hz (Clear.odd_coprime_four ho) k hk).2),hp,eval_zero,zero_div]

end Roots
end
end GuoWang.Block
```

### `GWProperDivisors.lean`

```lean
import GWBlockTerms

namespace GuoWang.Block
open Polynomial
noncomputable section

lemma range_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (d l : ℕ) :
    (∑ k ∈ Finset.range (l*d), f k) = ∑ u ∈ Finset.range l, ∑ r ∈ Finset.range d, f (u*d+r) := by
  induction l with
  | zero => simp
  | succ l ih => rw [Nat.succ_mul,Finset.sum_range_add,Finset.sum_range_succ,ih]

lemma block_parameters {d : ℕ} (hd : 0 < d) (ho : Odd d) (b : Bool) :
    ∃ h t : ℕ, d.Coprime (stride b) ∧ h < d ∧ 1+stride b*h=t*d := by
  obtain ⟨ha,hb⟩ := Clear.odd_zero_indices ho hd
  cases b
  · obtain ⟨h,hh,t,ht⟩ := hb
    exact ⟨h,t,Clear.odd_coprime_four ho,hh,by simpa only [stride,Bool.false_eq_true,ite_false,mul_comm] using ht⟩
  · obtain ⟨h,hh,t,ht⟩ := ha
    exact ⟨h,t,ho.coprime_two_right,hh,by simpa only [stride,ite_true,mul_comm] using ht⟩

variable {K : Type*} [Field K] [CharZero K] {z : K} {d : ℕ}

/-- Every multiple of an odd order has both individual sums zero there, with
regularity supplied by the cancelled representatives. -/
theorem family_multiple_value (hz : IsPrimitiveRoot z d) (hd : 1 < d) (ho : Odd d)
    (b : Bool) (m : ℕ) : HasValue z (∑ k ∈ Finset.range (m*d), source b k) 0 := by
  obtain ⟨h,t,hs,hh,ht⟩ := block_parameters (by omega) ho b
  have hv (l : ℕ) : HasValue z (∑ r ∈ Finset.range d, source b (l*d+r)) 0 := by
    have hv' := HasValue.sum (Finset.range d) _ _ (fun r hr =>
      source_block_value hz hd ho b h t l r hs hh ht (Finset.mem_range.mp hr))
    rw [← Finset.mul_sum,family_sum_root hz hd ho b,mul_zero] at hv'
    exact hv'
  rw [range_blocks]
  have hv' := HasValue.sum (Finset.range m) _ (fun _ => (0:K)) (fun l _ => hv l)
  simpa only [Finset.sum_const_zero] using hv'

end
end GuoWang.Block

namespace GuoWang
open Polynomial
noncomputable section

/-- Includes every composite-order factor; no common denominator is declared
a unit at a proper divisor. -/
theorem proper_cyclotomic (n d : ℕ) ( _hn : 0 < n) (h4 : n % 4 = 1)
    (hdn : d ∣ n) (hd : 1 < d) : cyclotomic d ℚ ∣ (diff n).num := by
  have ho : Odd n := ⟨2*(n/4),by omega⟩
  have hod : Odd d := by
    have hc := ho.coprime_two_right.of_dvd_left hdn
    exact Nat.odd_iff.mpr (by
      by_contra he
      have he' : d%2=0 := by omega
      have hg := hc.gcd_eq_one
      rw [Nat.gcd_comm,Nat.gcd_rec,he'] at hg
      norm_num at hg)
  let z := Complex.exp (2*Real.pi*Complex.I/d)
  have hz : IsPrimitiveRoot z d := Complex.isPrimitiveRoot_exp d (by omega)
  obtain ⟨m,hm⟩ := hdn
  have ha := Block.family_multiple_value hz hd hod true m
  have hb := Block.family_multiple_value hz hd hod false m
  have hv := ha.sub hb
  rw [show m*d = n by rw [hm,Nat.mul_comm],sub_self] at hv
  apply HasValue.cyclotomic_dvd_num (by omega) hz
  simpa only [Block.source,Bool.false_eq_true,ite_false,ite_true,diff] using hv

end
end GuoWang
```

### `GWConjecture.lean`

```lean
import GWTopFourth
import GWProperDivisors
import GWAssemble

namespace GuoWang
open Polynomial

/-- Guo–Wang Conjecture 4.1, with exactly the review's hypotheses and modulus. -/
theorem guo_wang_conj_4_1 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    qIntPoly n * (cyclotomic n ℚ)^3 ∣ (diff n).num := by
  by_cases h : n = 1
  · subst n
    exact guo_wang_conj_4_1_one
  · exact assemble_modulus n hn (by omega) _ (top_fourth n hn h4)
      (fun d hd hlarge _ => proper_cyclotomic n d hn h4 hd hlarge)

#print guo_wang_conj_4_1
#print axioms guo_wang_conj_4_1
#print axioms poch_den_ne_zero
#print axioms term_den_ne_zero

example : Conjecture41 := guo_wang_conj_4_1
end GuoWang
```

### `GWAuditR4.lean`

```lean
import GWConjecture

namespace GuoWang
open Polynomial

/-- Expanded source form, checked against the literal finite sums. -/
theorem reviewed_source_form (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    (∑ j ∈ Finset.range n, (X : ℚ[X])^j) * (cyclotomic n ℚ)^3 ∣
    ((∑ k ∈ Finset.range n,
      (-1)^k * (∑ j ∈ Finset.range (6*k+1), X'^j) * poch X' (X'^2) k ^ 3 /
        poch (X'^4) (X'^4) k ^ 3 * X'^(3*k^2)) -
     ∑ k ∈ Finset.range n,
      (-1)^k * (∑ j ∈ Finset.range (8*k+1), X'^j) * poch X' (X'^4) k ^ 3 /
        poch (X'^4) (X'^4) k ^ 3 * X'^(2*k^2+k)).num := by
  simpa only [qIntPoly,diff,L,R,qInt_eq_sum] using guo_wang_conj_4_1 n hn h4

theorem endpoint_denominators_nonzero (k : ℕ) :
    poch (X'^4) (X'^4) k ≠ 0 ∧ poch (X'^4) (X'^4) k ^ 3 ≠ 0 ∧ (1-X') ≠ 0 :=
  ⟨poch_den_ne_zero k,term_den_ne_zero k,by simpa using one_sub_X'_pow_ne_zero 1 (by omega)⟩

example : Conjecture41 := guo_wang_conj_4_1

#eval Lean.versionString
#check @guo_wang_conj_4_1
#check @reviewed_source_form
#check @endpoint_denominators_nonzero
#print poch
#print qIntPoly
#print qInt
#print X'
#print L
#print R
#print diff
#print axioms guo_wang_conj_4_1
#print axioms reviewed_source_form
#print axioms endpoint_denominators_nonzero
#print axioms top_fourth
#print axioms proper_cyclotomic
#print axioms Clear.polynomial_recurrence
#print axioms Clear.actual_operator_sq
#print axioms Clear.at_P_qn
#print axioms Clear.at_P_qn_inverse
#print axioms Clear.family_poly_root_zero
#print axioms Block.block_value
#print axioms Block.ratio_value
#print axioms Block.source_block_value
#print axioms Block.family_multiple_value
end GuoWang
```

### `GWNonVacuity.lean`

```lean
import GWClearSpecialize

/-! Non-vacuity: the literal difference is not the zero rational function
already for n = 5, so `(diff n).num` is not trivially divisible by everything. -/
namespace GuoWang.Clear
open Polynomial
open scoped BigOperators
noncomputable section

theorem erase_range_five :
    (Finset.range 5).erase 0 = {1,2,3,4} ∧ (Finset.range 5).erase 1 = {0,2,3,4} ∧
    (Finset.range 5).erase 2 = {0,1,3,4} ∧ (Finset.range 5).erase 3 = {0,1,2,4} ∧
    (Finset.range 5).erase 4 = {0,1,2,3} := by decide

theorem eval_two_Pone_five : ((Pone 5).eval 2 : ℚ) ≠ 0 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := erase_range_five
  simp only [Pone, P, commonNum, complement, num, den, Finset.sum_range_succ,
    Finset.sum_range_zero, h0, h1, h2, h3, h4]
  norm_num [Finset.prod_range_succ, Finset.sum_range_succ]

/-- The literal source difference for n = 5 is a nonzero rational function. -/
theorem diff_five_ne_zero : GuoWang.diff 5 ≠ 0 := by
  rw [diff_fraction]
  refine div_ne_zero ?_ ?_
  · intro h
    apply eval_two_Pone_five
    rw [(map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h, eval_zero]
  · intro h
    exact Hone_ne_zero 5 ((map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mp h)

/-- Hence its reduced numerator is a nonzero polynomial. -/
theorem diff_five_num_ne_zero : (GuoWang.diff 5).num ≠ 0 :=
  RatFunc.num_ne_zero diff_five_ne_zero

#print axioms diff_five_ne_zero
#print axioms diff_five_num_ne_zero

end
end GuoWang.Clear
```

### `GWReviewEndpoint.lean`

```lean
import GWAuditR4
import GWNonVacuity

/-! Final fidelity audit (stage 5). The block below is the "Required Lean
endpoint" of REVIEW-366674.md, copied character for character into its own
namespace, with the review's definitions rather than the lane's. The theorem is
then closed by the lane's proof; this checks that the two statements agree up
to definitional unfolding. -/
namespace ReviewEndpoint
noncomputable section

open Polynomial
-- base field ℚ; q is RatFunc.X
def poch (z b : RatFunc ℚ) (k : ℕ) : RatFunc ℚ := ∏ j ∈ Finset.range k, (1 - z * b ^ j)
def qInt (m : ℕ) : RatFunc ℚ := algebraMap _ _ (∑ j ∈ Finset.range m, (X : ℚ[X]) ^ j)   -- [m] as a polynomial, no division
def X' : RatFunc ℚ := RatFunc.X
def L (k : ℕ) : RatFunc ℚ := (-1) ^ k * qInt (6*k+1) * poch X' (X'^2) k ^ 3 / poch (X'^4) (X'^4) k ^ 3 * X' ^ (3*k^2)
def R (k : ℕ) : RatFunc ℚ := (-1) ^ k * qInt (8*k+1) * poch X' (X'^4) k ^ 3 / poch (X'^4) (X'^4) k ^ 3 * X' ^ (2*k^2+k)
def diff (n : ℕ) : RatFunc ℚ := ∑ k ∈ Finset.range n, L k - ∑ k ∈ Finset.range n, R k
theorem guo_wang_conj_4_1 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    (∑ j ∈ Finset.range n, (X : ℚ[X]) ^ j) * (cyclotomic n ℚ) ^ 3 ∣ (diff n).num :=
  GuoWang.guo_wang_conj_4_1 n hn h4
-- required side lemma, proved: ∀ k, poch (X'^4) (X'^4) k ≠ 0
theorem poch_side_lemma : ∀ k, poch (X'^4) (X'^4) k ≠ 0 :=
  GuoWang.poch_den_ne_zero

/-- The review's `diff` is literally the lane's `diff`. -/
theorem diff_eq_lane (n : ℕ) : diff n = GuoWang.diff n := rfl

/-- Non-vacuity for the review's own definitions. -/
theorem diff_five_ne_zero : diff 5 ≠ 0 := GuoWang.Clear.diff_five_ne_zero
theorem diff_five_num_ne_zero : (diff 5).num ≠ 0 := GuoWang.Clear.diff_five_num_ne_zero

end
end ReviewEndpoint

#check @ReviewEndpoint.guo_wang_conj_4_1
#check @ReviewEndpoint.poch_side_lemma
#check @ReviewEndpoint.diff_five_num_ne_zero
#print ReviewEndpoint.diff
#print ReviewEndpoint.L
#print ReviewEndpoint.R
#print ReviewEndpoint.qInt
#print ReviewEndpoint.poch
#print axioms ReviewEndpoint.guo_wang_conj_4_1
#print axioms ReviewEndpoint.poch_side_lemma
#print axioms ReviewEndpoint.diff_eq_lane
#print axioms ReviewEndpoint.diff_five_ne_zero
#print axioms ReviewEndpoint.diff_five_num_ne_zero
#print axioms GuoWang.guo_wang_conj_4_1
#print axioms GuoWang.reviewed_source_form
```
