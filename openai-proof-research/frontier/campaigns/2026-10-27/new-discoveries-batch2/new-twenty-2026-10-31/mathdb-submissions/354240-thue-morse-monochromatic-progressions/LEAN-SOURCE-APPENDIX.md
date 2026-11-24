# Complete Lean source appendix

Modules are in import order. The bytes inside each Lean block equal src/ exactly.

### `TmCore.lean`

```lean
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Polynomial
namespace TmCore
abbrev F := ZMod 2
abbrev R := Polynomial F

lemma euler_derivative_sub (p q : R) :
    X * derivative (p - q) = X * derivative p - X * derivative q := by
  rw [derivative_sub, mul_sub]

lemma euler_derivative_pow (p : R) (E : ℕ) :
    X * derivative (p ^ E) = C (E : F) * p ^ (E - 1) * (X * derivative p) := by
  rw [derivative_pow]
  ring

lemma euler_monomial (a : ℕ) :
    X * derivative (X ^ a : R) = C (a : F) * X ^ a := by
  rw [derivative_X_pow]
  cases a with
  | zero => simp
  | succ a => simp [pow_succ]; ring

lemma y_derivative : derivative (X + 1 : R) = 1 := by simp

lemma x_plus_one_ne_zero : (X + 1 : R) ≠ 0 := by
  simpa using (monic_X_add_C (1 : F)).ne_zero

lemma linear_factor_dvd (u : ℕ) : (X + 1 : R) ∣ 1 + X ^ u := by
  have h : (X - C (-1 : F)) ∣ (1 + X ^ u : R) := by
    apply dvd_iff_isRoot.mpr
    have hn : (-1 : F) = 1 := by decide
    simp only [IsRoot, eval_add, eval_one, eval_pow, eval_X, hn, one_pow]
    decide
  simpa only [map_neg, map_one, sub_neg_eq_add] using h

lemma compression_obstruction (B D u a H : ℕ) (Q : R)
    (hDB : D ≤ B) (hQ : Q ≠ 0)
    (hmod : (X + 1 : R) ^ B ∣ Q - X ^ a * (1 + X ^ u) ^ D)
    (hdeg : Q.natDegree ≤ H) : D ≤ H := by
  have hp : (X + 1 : R) ^ D ∣ (1 + X ^ u) ^ D :=
    pow_dvd_pow_of_dvd (linear_factor_dvd u) D
  have hm : (X + 1 : R) ^ D ∣ X ^ a * (1 + X ^ u) ^ D :=
    dvd_mul_of_dvd_right hp _
  have hb : (X + 1 : R) ^ D ∣ (X + 1) ^ B :=
    pow_dvd_pow _ hDB
  have hdiff := hb.trans hmod
  have hq : (X + 1 : R) ^ D ∣ Q := by
    have := dvd_add hdiff hm
    simpa using this
  have hdegree := ((monic_X_add_C (1 : F)).pow D).natDegree_le_of_dvd hQ hq
  change ((X + C (1 : F)) ^ D).natDegree ≤ Q.natDegree at hdegree
  have hdegree' : D ≤ Q.natDegree := by simpa only [natDegree_pow_X_add_C] using hdegree
  exact hdegree'.trans hdeg

lemma dyadic_modulus (e : ℕ) : (X + 1 : R) ^ (2 ^ e) = X ^ (2 ^ e) + 1 := by
  simpa using add_pow_char_pow (X : R) 1 2 e

lemma derivative_preserves_modulus (M : ℕ) (hM : (M : F) = 0)
    (P : R) (h : (X + 1 : R) ^ M ∣ P) :
    (X + 1 : R) ^ M ∣ derivative P := by
  obtain ⟨Q, rfl⟩ := h
  rw [derivative_mul, derivative_pow, hM]
  simp only [map_zero, zero_mul, zero_add]
  exact dvd_mul_right _ _

lemma euler_binomial (u E : ℕ) (hu : (u : F) = 1) (hE : (E : F) = 1) :
    X * derivative ((1 + X ^ u : R) ^ E) =
      X ^ u * (1 + X ^ u) ^ (E - 1) := by
  rw [euler_derivative_pow, hE, map_one, one_mul]
  have hp : (X : R) * derivative (1 + X ^ u) = X ^ u := by
    rw [derivative_add, derivative_one, zero_add, euler_monomial, hu, map_one, one_mul]
  rw [hp, mul_comm]

lemma euler_product (a E : ℕ) (hE : (E : F) = 1) :
    X * derivative ((X : R) ^ a * (X + 1) ^ E) =
      C (a : F) * X ^ a * (X + 1) ^ E + X ^ (a + 1) * (X + 1) ^ (E - 1) := by
  calc
    _ = (X * derivative (X ^ a)) * (X + 1) ^ E +
        X ^ a * (X * derivative ((X + 1) ^ E)) := by
      rw [derivative_mul]
      ring
    _ = _ := by
      rw [euler_monomial, euler_derivative_pow, y_derivative, hE, map_one]
      simp only [one_mul, mul_one, pow_succ]
      ring

lemma euler_rigidity_congruence (M E u a : ℕ)
    (hEpos : 1 ≤ E) (hEM : E ≤ M)
    (hM : (M : F) = 0) (hE : (E : F) = 1) (hu : (u : F) = 1)
    (h : (X + 1 : R) ^ M ∣ (1 + X ^ u) ^ E - X ^ a * (X + 1) ^ E) :
    (X + 1 : R) ^ (M - E + 1) ∣
      X ^ a * (X ^ u - X - C (a : F) * (X + 1) * (1 + X ^ u)) := by
  have hd := derivative_preserves_modulus M hM _ h
  have hd' := dvd_mul_of_dvd_right hd (X : R)
  rw [euler_derivative_sub, euler_binomial u E hu hE, euler_product a E hE] at hd'
  have h1 := dvd_mul_of_dvd_right hd' (1 + X ^ u : R)
  have h0 := dvd_mul_of_dvd_right h (X ^ u : R)
  have hR := dvd_sub h1 h0
  have hp : (1 + X ^ u : R) ^ E = (1 + X ^ u) ^ (E - 1) * (1 + X ^ u) := by
    rw [← pow_succ, Nat.sub_add_cancel hEpos]
  have hy : (X + 1 : R) ^ E = (X + 1) ^ (E - 1) * (X + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hEpos]
  have hid :
      (1 + X ^ u : R) *
          (X ^ u * (1 + X ^ u) ^ (E - 1) -
            (C (a : F) * X ^ a * (X + 1) ^ E + X ^ (a + 1) * (X + 1) ^ (E - 1))) -
        X ^ u * ((1 + X ^ u) ^ E - X ^ a * (X + 1) ^ E) =
      (X + 1) ^ (E - 1) *
        (X ^ a * (X ^ u - X - C (a : F) * (X + 1) * (1 + X ^ u))) := by
    rw [hp, hy]
    simp only [pow_succ]
    ring
  rw [hid] at hR
  obtain ⟨Z, hZ⟩ := hR
  refine ⟨Z, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (E - 1) x_plus_one_ne_zero)
  have hexp : (E - 1) + (M - E + 1) = M := by omega
  have hpow : (X + 1 : R) ^ M = (X + 1) ^ (E - 1) * (X + 1) ^ (M - E + 1) := by
    rw [← pow_add, hexp]
  rw [hpow] at hZ
  simpa only [mul_assoc] using hZ

lemma binomial_nonzero (n : ℕ) (hn : 0 < n) : (1 + X ^ n : R) ≠ 0 := by
  intro h
  have he := congrArg (eval (0 : F)) h
  simp [hn.ne'] at he

lemma rootMultiplicity_pow_local (P : R) (hP : P ≠ 0) (n : ℕ) :
    (P ^ n).rootMultiplicity (1 : F) = n * P.rootMultiplicity (1 : F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hP) hP), ih]
    simp [Nat.succ_mul]

lemma odd_binomial_rootMultiplicity (n : ℕ) (hn : 0 < n) (hc : (n : F) = 1) :
    (1 + X ^ n : R).rootMultiplicity (1 : F) = 1 := by
  have hp := binomial_nonzero n hn
  have hr : (1 + X ^ n : R).IsRoot (1 : F) := by
    simp only [IsRoot, eval_add, eval_one, eval_pow, eval_X, one_pow]
    decide
  have hl : 1 ≤ (1 + X ^ n : R).rootMultiplicity (1 : F) :=
    (rootMultiplicity_pos hp).2 hr
  have hder : ¬ (derivative (1 + X ^ n : R)).IsRoot (1 : F) := by
    simp only [derivative_add, derivative_one, zero_add, derivative_X_pow, IsRoot,
      eval_mul, eval_C, eval_pow, eval_X, hc, one_pow, mul_one]
    exact one_ne_zero
  have hu : ¬ 1 < (1 + X ^ n : R).rootMultiplicity (1 : F) := by
    intro hlt
    exact hder ((one_lt_rootMultiplicity_iff_isRoot hp).1 hlt).2
  omega

lemma odd_natCast (n : ℕ) (hn : Odd n) : (n : F) = 1 :=
  hn.natCast_zmod_two

lemma binomial_two_pow_rootMultiplicity (k m : ℕ) (hm : 0 < m) (hc : (m : F) = 1) :
    (1 + X ^ (2 ^ k * m) : R).rootMultiplicity (1 : F) = 2 ^ k := by
  have hid : (1 + X ^ m : R) ^ (2 ^ k) = 1 + X ^ (2 ^ k * m) := by
    rw [add_pow_char_pow (1 : R) (X ^ m) 2 k, one_pow, ← pow_mul, Nat.mul_comm m]
  rw [← hid, rootMultiplicity_pow_local _ (binomial_nonzero m hm),
    odd_binomial_rootMultiplicity m hm hc, Nat.mul_one]

lemma monomial_rootMultiplicity (a : ℕ) : (X ^ a : R).rootMultiplicity (1 : F) = 0 := by
  apply rootMultiplicity_eq_zero
  simp only [IsRoot, eval_pow, eval_X, one_pow]
  exact one_ne_zero

lemma high_multiplicity_obstruction (e K a h : ℕ)
    (hh : 0 < h) (hmax : h < 2 ^ e)
    (hdiv : (X + 1 : R) ^ K ∣ X ^ a * (1 + X ^ h)) : 2 * K ≤ 2 ^ e := by
  obtain ⟨k, m, hm, heq⟩ := Nat.exists_eq_two_pow_mul_odd hh.ne'
  have hmpos : 0 < m := by
    obtain ⟨z, hz⟩ := hm
    omega
  have hp : (X ^ a * (1 + X ^ h) : R) ≠ 0 :=
    mul_ne_zero (pow_ne_zero a X_ne_zero) (binomial_nonzero h hh)
  have hsub : (X - C (1 : F) : R) = X + 1 := by
    rw [map_one, CharTwo.sub_eq_add]
  have hroot : K ≤ (X ^ a * (1 + X ^ h) : R).rootMultiplicity (1 : F) := by
    apply (le_rootMultiplicity_iff hp).2
    simpa only [hsub] using hdiv
  rw [rootMultiplicity_mul hp, monomial_rootMultiplicity, zero_add, heq,
    binomial_two_pow_rootMultiplicity k m hmpos (odd_natCast m hm)] at hroot
  have hk : k < e := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
    have hle : 2 ^ k ≤ h := by
      rw [heq]
      exact Nat.le_mul_of_pos_right _ hmpos
    omega
  have hpow : 2 ^ (k + 1) ≤ 2 ^ e :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  calc
    2 * K ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hroot
    _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ 2 ^ e := hpow

/-- The odd, primitive core of affine binomial-cube rigidity. -/
lemma primitive_affine_rigidity (e E u a : ℕ)
    (he : 0 < e) (hEpos : 1 ≤ E) (hsmall : 2 * E < 2 ^ e)
    (hupos : 1 ≤ u) (humax : u < 2 ^ e)
    (hE : (E : F) = 1) (hu : (u : F) = 1)
    (h : (X + 1 : R) ^ (2 ^ e) ∣
      (1 + X ^ u) ^ E - X ^ a * (X + 1) ^ E) :
    u = 1 ∨ u + 1 = 2 ^ e := by
  have hM : ((2 ^ e : ℕ) : F) = 0 := by
    rw [Nat.cast_pow]
    change (2 : F) ^ e = 0
    simp only [CharTwo.two_eq_zero (R := F), zero_pow he.ne']
  have hEM : E ≤ 2 ^ e := by omega
  have hpoly := euler_rigidity_congruence (2 ^ e) E u a hEpos hEM hM hE hu h
  have hlarge : 2 ^ e < 2 * (2 ^ e - E + 1) := by omega
  rcases CharTwo.natCast_cases (R := F) a with ha | ha
  · simp only [ha, map_zero, zero_mul, sub_zero] at hpoly
    by_cases hunit : u = 1
    · exact Or.inl hunit
    have hh : 0 < u - 1 := by omega
    have hhmax : u - 1 < 2 ^ e := by omega
    have hxp : (X : R) ^ u = X ^ (u - 1) * X := by
      rw [← pow_succ, Nat.sub_add_cancel hupos]
    have hid : (X ^ a * (X ^ u - X) : R) = X ^ (a + 1) * (1 + X ^ (u - 1)) := by
      rw [CharTwo.sub_eq_add, hxp, pow_succ]
      ring
    rw [hid] at hpoly
    have := high_multiplicity_obstruction e (2 ^ e - E + 1) (a + 1) (u - 1) hh hhmax hpoly
    omega
  · simp only [ha, map_one, one_mul] at hpoly
    have hid : (X ^ u - X - (X + 1) * (1 + X ^ u) : R) = 1 + X ^ (u + 1) := by
      calc
        _ = (X ^ u + X ^ u) + (X + X) + (1 + X ^ (u + 1)) := by
          simp only [CharTwo.sub_eq_add, pow_succ]
          ring
        _ = _ := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add]
    rw [hid] at hpoly
    by_cases hlast : u + 1 = 2 ^ e
    · exact Or.inr hlast
    have hh : 0 < u + 1 := by omega
    have hhmax : u + 1 < 2 ^ e := by omega
    have := high_multiplicity_obstruction e (2 ^ e - E + 1) a (u + 1) hh hhmax hpoly
    omega

#print axioms primitive_affine_rigidity

#print axioms binomial_two_pow_rootMultiplicity
#print axioms high_multiplicity_obstruction

#print axioms odd_natCast
#print axioms odd_binomial_rootMultiplicity
#print axioms euler_rigidity_congruence
#print axioms derivative_preserves_modulus
#print axioms euler_binomial
#print axioms euler_product
#print axioms dyadic_modulus
#print axioms compression_obstruction
#print axioms euler_derivative_pow
#print axioms euler_monomial
end TmCore
```

### `TmCyclic.lean`

```lean
import TmCore
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.ModEq

open Polynomial
open scoped BigOperators
namespace TmCyclic
open TmCore

lemma monomial_reduction (e n : ℕ) :
    (X + 1 : R) ^ (2 ^ e) ∣ X ^ n - X ^ (n % (2 ^ e)) := by
  have hbase : (X + 1 : R) ^ (2 ^ e) = X ^ (2 ^ e) - 1 := by
    rw [dyadic_modulus, CharTwo.sub_eq_add]
  have hp : (X + 1 : R) ^ (2 ^ e) ∣ (X ^ (2 ^ e)) ^ (n / (2 ^ e)) - 1 := by
    rw [hbase]
    simpa only [one_pow] using sub_dvd_pow_sub_pow (X ^ (2 ^ e) : R) 1 (n / (2 ^ e))
  have hm := dvd_mul_of_dvd_right hp (X ^ (n % (2 ^ e)) : R)
  have hid : (X ^ (n % (2 ^ e)) : R) * ((X ^ (2 ^ e)) ^ (n / (2 ^ e)) - 1) =
      X ^ n - X ^ (n % (2 ^ e)) := by
    rw [mul_sub, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [hid] at hm
  exact hm

lemma reduction_sum (e : ℕ) (S : Finset ℕ) (f : ℕ → ℕ) :
    (X + 1 : R) ^ (2 ^ e) ∣
      (∑ z ∈ S, X ^ (f z) : R) - ∑ z ∈ S, X ^ ((f z) % (2 ^ e)) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum (fun z _ => monomial_reduction e (f z))

lemma indicator_nonzero (S : Finset ℕ) (f : ℕ → ℕ) (hS : S.Nonempty)
    (hinj : Set.InjOn f (↑S : Set ℕ)) : (∑ z ∈ S, X ^ (f z) : R) ≠ 0 := by
  obtain ⟨z, hz⟩ := hS
  have hc : (∑ y ∈ S, X ^ (f y) : R).coeff (f z) = 1 := by
    rw [finsetSum_coeff, Finset.sum_eq_single z]
    · simp
    · intro y hy hyz
      have hne : f y ≠ f z := by
        intro heq
        exact hyz (hinj hy hz heq)
      simp [hne.symm]
    · exact fun h => False.elim (h hz)
  intro hzero
  rw [hzero, coeff_zero] at hc
  exact zero_ne_one hc

lemma indicator_degree (S : Finset ℕ) (f : ℕ → ℕ) (H : ℕ)
    (hbound : ∀ z ∈ S, f z ≤ H) : (∑ z ∈ S, X ^ (f z) : R).natDegree ≤ H := by
  exact natDegree_sum_le_of_forall_le S _ (fun z hz => by simpa using hbound z hz)

lemma affine_reduction_injective (B u a : ℕ) (S : Finset ℕ)
    (hcop : Nat.Coprime B u) (hS : ∀ z ∈ S, z < B) :
    Set.InjOn (fun z => (a + u * z) % B) (↑S : Set ℕ) := by
  intro x hx y hy heq
  have hmod : a + u * x ≡ a + u * y [MOD B] := heq
  have hmod' : u * x ≡ u * y [MOD B] := hmod.add_left_cancel' a
  have hxy : x ≡ y [MOD B] := Nat.ModEq.cancel_left_of_coprime hcop hmod'
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hS x hx), Nat.mod_eq_of_lt (hS y hy)] using hxy

/-- Compression for a binomial support, given its ordinary generating polynomial. -/
lemma finite_support_compression (e D u a H : ℕ) (S : Finset ℕ)
    (hD : D ≤ 2 ^ e) (hS : S.Nonempty) (hbound : ∀ z ∈ S, z < 2 ^ e)
    (hcop : Nat.Coprime (2 ^ e) u)
    (hpoly : (∑ z ∈ S, X ^ (a + u * z) : R) = X ^ a * (1 + X ^ u) ^ D)
    (harc : ∀ z ∈ S, (a + u * z) % (2 ^ e) ≤ H) : D ≤ H := by
  let Q : R := ∑ z ∈ S, X ^ ((a + u * z) % (2 ^ e))
  have hQ : Q ≠ 0 := indicator_nonzero S _ hS
    (affine_reduction_injective (2 ^ e) u a S hcop hbound)
  have hdeg : Q.natDegree ≤ H := indicator_degree S _ H harc
  have hmod := reduction_sum e S (fun z => a + u * z)
  rw [hpoly] at hmod
  have hmod' : (X + 1 : R) ^ (2 ^ e) ∣ Q - X ^ a * (1 + X ^ u) ^ D := by
    simpa only [Q, neg_sub] using dvd_neg.mpr hmod
  exact compression_obstruction (2 ^ e) D u a H Q hD hQ hmod' hdeg

#print axioms finite_support_compression
end TmCyclic
```

### `TmBinary.lean`

```lean
import TmCore
import Mathlib.Data.Nat.Digits.Defs

namespace TmBinary
open TmCore

/-- The actual binary digit-parity sequence, with zero-based indexing. -/
def tm (n : ℕ) : F := ((Nat.digits 2 n).sum : F)

@[simp] lemma tm_zero : tm 0 = 0 := by simp [tm]

@[simp] lemma tm_two_mul (n : ℕ) : tm (2 * n) = tm n := by
  by_cases hn : n = 0
  · subst n; simp
  have hd := Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr hn)
  simpa [tm] using congrArg (fun l : List ℕ => (l.sum : F)) hd

@[simp] lemma tm_two_mul_add_one (n : ℕ) : tm (2 * n + 1) = 1 + tm n := by
  have hd := Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))
  simpa [tm, Nat.add_comm] using congrArg (fun l : List ℕ => (l.sum : F)) hd

lemma tm_dyadic_block (e m r : ℕ) (hr : r < 2 ^ e) :
    tm (2 ^ e * m + r) = tm m + tm r := by
  induction e generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    subst r
    simp
  | succ e ih =>
    have hq : r / 2 < 2 ^ e := by
      have hp : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ, Nat.mul_comm]
      rw [hp] at hr
      omega
    have hp : 2 ^ (e + 1) * m = 2 * (2 ^ e * m) := by rw [pow_succ]; ring
    have hb : r % 2 = 0 ∨ r % 2 = 1 := by omega
    rcases hb with hb | hb
    · have hidx : 2 ^ (e + 1) * m + r = 2 * (2 ^ e * m + r / 2) := by
        rw [hp]
        omega
      have hridx : r = 2 * (r / 2) := by omega
      have htmr : tm r = tm (r / 2) := by
        calc
          tm r = tm (2 * (r / 2)) := congrArg tm hridx
          _ = tm (r / 2) := tm_two_mul _
      rw [hidx, tm_two_mul, ih _ hq, htmr]
    · have hidx : 2 ^ (e + 1) * m + r = 2 * (2 ^ e * m + r / 2) + 1 := by
        rw [hp]
        omega
      have hridx : r = 2 * (r / 2) + 1 := by omega
      have htmr : tm r = 1 + tm (r / 2) := by
        calc
          tm r = tm (2 * (r / 2) + 1) := congrArg tm hridx
          _ = 1 + tm (r / 2) := tm_two_mul_add_one _
      rw [hidx, tm_two_mul_add_one, ih _ hq, htmr]
      ring

lemma tm_dyadic_complement (e r : ℕ) (hr : r < 2 ^ e) :
    tm (2 ^ e - 1 - r) = (e : F) + tm r := by
  induction e generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    subst r
    simp
  | succ e ih =>
    have hp : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ, Nat.mul_comm]
    have hq : r / 2 < 2 ^ e := by rw [hp] at hr; omega
    have hb : r % 2 = 0 ∨ r % 2 = 1 := by omega
    rcases hb with hb | hb
    · have hidx : 2 ^ (e + 1) - 1 - r = 2 * (2 ^ e - 1 - r / 2) + 1 := by
        rw [hp]
        omega
      have hridx : r = 2 * (r / 2) := by omega
      have htmr : tm r = tm (r / 2) := by
        calc
          tm r = tm (2 * (r / 2)) := congrArg tm hridx
          _ = tm (r / 2) := tm_two_mul _
      rw [hidx, tm_two_mul_add_one, ih _ hq, htmr, Nat.cast_add, Nat.cast_one]
      ring
    · have hidx : 2 ^ (e + 1) - 1 - r = 2 * (2 ^ e - 1 - r / 2) := by
        rw [hp]
        omega
      have hridx : r = 2 * (r / 2) + 1 := by omega
      have htmr : tm r = 1 + tm (r / 2) := by
        calc
          tm r = tm (2 * (r / 2) + 1) := congrArg tm hridx
          _ = 1 + tm (r / 2) := tm_two_mul_add_one _
      rw [hidx, tm_two_mul, ih _ hq, htmr, Nat.cast_add, Nat.cast_one]
      simp only [add_assoc, CharTwo.add_cancel_left]

lemma tm_aligned_pair_ne (n : ℕ) : tm (2 * n) ≠ tm (2 * n + 1) := by
  rw [tm_two_mul, tm_two_mul_add_one]
  intro h
  have hzero : (1 : F) = 0 := by
    apply add_right_cancel (b := tm n)
    simpa only [zero_add] using h.symm
  exact one_ne_zero hzero

lemma tm_no_triple (n : ℕ) : ¬ (tm n = tm (n + 1) ∧ tm (n + 1) = tm (n + 2)) := by
  intro h
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hb | hb
  · have h0 : n = 2 * (n / 2) := by omega
    have h1 : n + 1 = 2 * (n / 2) + 1 := by omega
    exact tm_aligned_pair_ne _ ((congrArg tm h0).symm.trans (h.1.trans (congrArg tm h1)))
  · have h1 : n + 1 = 2 * (n / 2 + 1) := by omega
    have h2 : n + 2 = 2 * (n / 2 + 1) + 1 := by omega
    exact tm_aligned_pair_ne _ ((congrArg tm h1).symm.trans (h.2.trans (congrArg tm h2)))

lemma tm_no_odd_palindrome_five (M : ℕ) (hM : 2 ≤ M)
    (hinner : tm (M - 1) = tm (M + 1))
    (houter : tm (M - 2) = tm (M + 2)) : False := by
  let a := M / 2
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hplus1 : a - 1 + 1 = a := by omega
  have hplus2 : a - 1 + 2 = a + 1 := by omega
  rcases (show M % 2 = 0 ∨ M % 2 = 1 by omega) with hb | hb
  · have hi0 : M - 1 = 2 * (a - 1) + 1 := by dsimp [a]; omega
    have hi1 : M + 1 = 2 * a + 1 := by dsimp [a]; omega
    have ho0 : M - 2 = 2 * (a - 1) := by dsimp [a]; omega
    have ho1 : M + 2 = 2 * (a + 1) := by dsimp [a]; omega
    rw [hi0, hi1, tm_two_mul_add_one, tm_two_mul_add_one] at hinner
    rw [ho0, ho1, tm_two_mul, tm_two_mul] at houter
    have hleft : tm (a - 1) = tm a := add_left_cancel hinner
    apply tm_no_triple (a - 1)
    exact ⟨by simpa only [hplus1] using hleft,
      by simpa only [hplus1, hplus2] using hleft.symm.trans houter⟩
  · have hi0 : M - 1 = 2 * a := by dsimp [a]; omega
    have hi1 : M + 1 = 2 * (a + 1) := by dsimp [a]; omega
    have ho0 : M - 2 = 2 * (a - 1) + 1 := by dsimp [a]; omega
    have ho1 : M + 2 = 2 * (a + 1) + 1 := by dsimp [a]; omega
    rw [hi0, hi1, tm_two_mul, tm_two_mul] at hinner
    rw [ho0, ho1, tm_two_mul_add_one, tm_two_mul_add_one] at houter
    have hout : tm (a - 1) = tm (a + 1) := add_left_cancel houter
    apply tm_no_triple (a - 1)
    exact ⟨by simpa only [hplus1] using hout.trans hinner.symm,
      by simpa only [hplus1, hplus2] using hinner⟩

def Mono (n d L : ℕ) : Prop := ∀ i : ℕ, i < L → tm (n + i * d) = tm n

lemma tm_even_step (n d i : ℕ) :
    tm (n + i * (2 * d)) = tm (n / 2 + i * d) + tm (n % 2) := by
  have hidx : n + i * (2 * d) = 2 * (n / 2 + i * d) + n % 2 := by
    have hi : i * (2 * d) = 2 * (i * d) := by ring
    rw [hi]
    omega
  rw [hidx]
  exact tm_dyadic_block 1 _ _ (by omega)

lemma mono_double_iff (n d L : ℕ) : Mono n (2 * d) L ↔ Mono (n / 2) d L := by
  have hbase : tm n = tm (n / 2) + tm (n % 2) := by
    simpa only [Nat.zero_mul, Nat.add_zero] using tm_even_step n d 0
  constructor
  · intro h i hi
    apply add_right_cancel (b := tm (n % 2))
    rw [← tm_even_step n d i, ← hbase]
    exact h i hi
  · intro h i hi
    rw [tm_even_step, hbase, h i hi]

#print axioms tm_no_odd_palindrome_five
#print axioms mono_double_iff

#print axioms tm_dyadic_block
#print axioms tm_dyadic_complement
end TmBinary
```

### `TmCube.lean`

```lean
import TmCyclic
import TmBinary
import Mathlib.Data.Nat.Choose.Lucas

open Polynomial
open scoped BigOperators
namespace TmCube
open TmCore TmCyclic TmBinary

lemma f2_cases (c : F) : c = 0 ∨ c = 1 := by
  have h : ∀ c : F, c = 0 ∨ c = 1 := by decide
  exact h c

lemma f2_eq_one_of_ne_zero (c : F) (hc : c ≠ 0) : c = 1 :=
  (f2_cases c).resolve_left hc

noncomputable def cube (D : ℕ) : Finset ℕ := ((1 + X : R) ^ D).support

lemma cube_nonempty (D : ℕ) : (cube D).Nonempty := by
  apply support_nonempty.mpr
  apply pow_ne_zero
  simpa only [add_comm] using x_plus_one_ne_zero

lemma cube_mem_le (D z : ℕ) (hz : z ∈ cube D) : z ≤ D := by
  have hle := le_natDegree_of_mem_supp z hz
  have hdeg : ((1 + X : R) ^ D).natDegree = D := by
    rw [add_comm]
    simpa only [map_one] using natDegree_pow_X_add_C D (1 : F)
  exact hdeg ▸ hle

lemma cube_coeff_one (D z : ℕ) (hz : z ∈ cube D) : ((1 + X : R) ^ D).coeff z = 1 := by
  apply f2_eq_one_of_ne_zero
  exact mem_support_iff.mp hz

lemma cube_indicator (D : ℕ) : (∑ z ∈ cube D, X ^ z : R) = (1 + X) ^ D := by
  calc
    _ = ∑ z ∈ cube D, C (((1 + X : R) ^ D).coeff z) * X ^ z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [cube_coeff_one D z hz, map_one, one_mul]
    _ = _ := by
      simpa only [cube, sum_def] using sum_C_mul_X_pow_eq ((1 + X : R) ^ D)

lemma cube_generating (D u a : ℕ) :
    (∑ z ∈ cube D, X ^ (a + u * z) : R) = X ^ a * (1 + X ^ u) ^ D := by
  calc
    _ = X ^ a * ((∑ z ∈ cube D, X ^ z : R).comp (X ^ u)) := by
      rw [sum_comp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [pow_comp, X_comp, ← pow_mul, ← pow_add]
    _ = _ := by rw [cube_indicator]; simp

lemma cube_compression (e D u a H : ℕ)
    (hD : D < 2 ^ e) (hcop : Nat.Coprime (2 ^ e) u)
    (harc : ∀ z ∈ cube D, (a + u * z) % (2 ^ e) ≤ H) : D ≤ H := by
  apply finite_support_compression e D u a H (cube D) hD.le (cube_nonempty D)
    (fun z hz => (cube_mem_le D z hz).trans_lt hD) hcop (cube_generating D u a) harc

#print axioms cube_compression
end TmCube
```

### `TmReflection.lean`

```lean
import TmCube

open Polynomial
namespace TmReflection
open TmCore TmBinary TmCube

lemma tm_small (n : ℕ) (hn : n < 2) : tm n = (n : F) := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · simp
  · decide

lemma tm_half (n : ℕ) : tm n = (n % 2 : ℕ) + tm (n / 2) := by
  have h := tm_dyadic_block 1 (n / 2) (n % 2) (by omega)
  have hi : 2 ^ 1 * (n / 2) + n % 2 = n := by omega
  rw [hi, tm_small (n % 2) (by omega)] at h
  simpa only [add_comm] using h

lemma choose_half (D z : ℕ) (hc : (D.choose z : F) = 1) :
    ((D / 2).choose (z / 2) : F) = 1 ∧ z % 2 ≤ D % 2 := by
  have hl : (D.choose z : F) =
      (((D % 2).choose (z % 2) : ℕ) : F) * ((D / 2).choose (z / 2) : F) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ 2).2
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := D) (k := z) (p := 2))
    simpa only [Nat.cast_mul] using h
  rw [hc] at hl
  have hDbits : D % 2 = 0 ∨ D % 2 = 1 := by omega
  have hzbits : z % 2 = 0 ∨ z % 2 = 1 := by omega
  rcases hDbits with hd | hd
  · rcases hzbits with hz | hz
    · exact ⟨by simpa only [hd, hz, Nat.choose_zero_right, Nat.cast_one, one_mul] using hl.symm,
        by omega⟩
    · norm_num [hd, hz] at hl
  · rcases hzbits with hz | hz
    · exact ⟨by simpa only [hd, hz, Nat.choose_zero_right, Nat.cast_one, one_mul] using hl.symm,
        by omega⟩
    · exact ⟨by simpa only [hd, hz, Nat.choose_self, Nat.cast_one, one_mul] using hl.symm,
        by omega⟩

lemma choose_reflection (D z : ℕ) (hc : (D.choose z : F) = 1) :
    tm z + tm (D - z) = tm D := by
  induction D using Nat.strong_induction_on generalizing z with
  | h D ih =>
    have hzle : z ≤ D := by
      by_contra hn
      have hgt : D < z := by omega
      rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero] at hc
      exact zero_ne_one hc
    by_cases hD : D = 0
    · have hz : z = 0 := by omega
      subst D; subst z; simp
    have hDpos : 0 < D := by omega
    obtain ⟨hcq, hbits⟩ := choose_half D z hc
    have hi := ih (D / 2) (Nat.div_lt_self hDpos (by decide)) (z / 2) hcq
    have hlow : z % 2 + (D - z) % 2 = D % 2 := by omega
    have hhigh : (D - z) / 2 = D / 2 - z / 2 := by omega
    calc
      _ = ((z % 2 + (D - z) % 2 : ℕ) : F) + (tm (z / 2) + tm ((D - z) / 2)) := by
        rw [tm_half z, tm_half (D - z), Nat.cast_add]
        ring
      _ = _ := by rw [hlow, hhigh, hi, ← tm_half]

lemma cube_reflection (D z : ℕ) (hz : z ∈ cube D) : tm z + tm (D - z) = tm D := by
  apply choose_reflection
  have h := cube_coeff_one D z hz
  simpa only [coeff_one_add_X_pow] using h

lemma choose_divisible (e D z : ℕ) (hD : 2 ^ e ∣ D) (hc : (D.choose z : F) = 1) :
    2 ^ e ∣ z := by
  induction e generalizing D z with
  | zero => simp
  | succ e ih =>
    obtain ⟨q, hq⟩ := hD
    have hDeq : D = 2 * (2 ^ e * q) := by rw [hq, pow_succ]; ring
    have hDmod : D % 2 = 0 := by omega
    obtain ⟨hcq, hbits⟩ := choose_half D z hc
    have hzmod : z % 2 = 0 := by omega
    have hDq : 2 ^ e ∣ D / 2 := ⟨q, by omega⟩
    obtain ⟨k, hk⟩ := ih (D / 2) (z / 2) hDq hcq
    refine ⟨k, ?_⟩
    rw [pow_succ]
    have hzeq : z = 2 * (z / 2) := by omega
    rw [hzeq, hk]
    ring

lemma tm_scale (e m : ℕ) : tm (2 ^ e * m) = tm m := by
  simpa only [Nat.add_zero, tm_zero, add_zero] using
    tm_dyadic_block e m 0 (by exact pow_pos (by decide) e)

lemma tm_add_low (e n j : ℕ) (hn : 2 ^ e ∣ n) (hj : j < 2 ^ e) :
    tm (n + j) = tm n + tm j := by
  obtain ⟨q, rfl⟩ := hn
  rw [tm_dyadic_block e q j hj, tm_scale]

lemma shifted_cube_reflection (e j D N z : ℕ)
    (hD : 2 ^ e ∣ D) (hj : j < 2 ^ e) (hN : N = D + 2 * j)
    (hz : z ∈ cube D) : tm (j + z) + tm (N - (j + z)) = tm D := by
  have hzle := cube_mem_le D z hz
  have hcz : (D.choose z : F) = 1 := by
    simpa only [coeff_one_add_X_pow] using cube_coeff_one D z hz
  have hzdiv := choose_divisible e D z hD hcz
  have hremdiv : 2 ^ e ∣ D - z := Nat.dvd_sub hD hzdiv
  have hidx : N - (j + z) = (D - z) + j := by omega
  have hswap : j + z = z + j := by omega
  rw [hidx, hswap, tm_add_low e z j hzdiv hj, tm_add_low e (D - z) j hremdiv hj]
  calc
    _ = (tm z + tm (D - z)) + (tm j + tm j) := by ring
    _ = _ := by rw [cube_reflection D z hz, CharTwo.add_self_eq_zero, add_zero]

#print axioms shifted_cube_reflection

#print axioms cube_reflection
end TmReflection
```

### `TmValuation.lean`

```lean
import TmReflection

namespace TmValuation
open TmCore TmBinary TmCube TmReflection

lemma tm_odd_successor (m : ℕ) (hm : Odd m) : tm m = 1 + tm (m - 1) := by
  obtain ⟨k, hk⟩ := hm
  have hmidx : m = 2 * k + 1 := by omega
  have hpidx : m - 1 = 2 * k := by omega
  have hp : tm (m - 1) = tm k := by rw [hpidx, tm_two_mul]
  calc
    tm m = tm (2 * k + 1) := congrArg tm hmidx
    _ = 1 + tm k := tm_two_mul_add_one k
    _ = 1 + tm (m - 1) := by rw [hp]

lemma tm_mersenne (e : ℕ) : tm (2 ^ e - 1) = (e : F) := by
  have h := tm_dyadic_complement e 0 (pow_pos (by decide) e)
  simpa only [Nat.sub_zero, tm_zero, add_zero] using h

lemma tm_dyadic_gap (v h : ℕ) (hle : h ≤ v) :
    tm (2 ^ v - 2 ^ h) = (v : F) + (h : F) := by
  have hpow : 2 ^ h ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hle
  have hpos : 0 < 2 ^ h := pow_pos (by decide) h
  have hr : 2 ^ h - 1 < 2 ^ v := by omega
  have hi : 2 ^ v - 1 - (2 ^ h - 1) = 2 ^ v - 2 ^ h := by omega
  have hc := tm_dyadic_complement v (2 ^ h - 1) hr
  rw [hi, tm_mersenne] at hc
  exact hc

lemma tm_sub_power_difference (v m h : ℕ) (hm : Odd m) (hle : h ≤ v) :
    tm (2 ^ v * m - 2 ^ h) + tm (2 ^ v * m) = 1 + (v : F) + (h : F) := by
  have hmpos : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  have hpow : 2 ^ h ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hle
  have hpos : 0 < 2 ^ h := pow_pos (by decide) h
  have hbase : 2 ^ v ≤ 2 ^ v * m := Nat.le_mul_of_pos_right _ hmpos
  have hi : 2 ^ v * m - 2 ^ h = 2 ^ v * (m - 1) + (2 ^ v - 2 ^ h) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  have hr : 2 ^ v - 2 ^ h < 2 ^ v := by omega
  rw [hi, tm_dyadic_block v (m - 1) _ hr, tm_scale, tm_dyadic_gap v h hle,
    tm_odd_successor m hm]
  calc
    _ = (1 + (v : F) + (h : F)) + (tm (m - 1) + tm (m - 1)) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

#print axioms tm_sub_power_difference
end TmValuation
```

### `TmClasses.lean`

```lean
import TmValuation

namespace TmClasses
open TmCore TmBinary TmCube TmReflection TmValuation

lemma f2_opposite (x y : F) (h : x ≠ y) : x = 1 + y := by
  have hs : ∀ x y : F, x ≠ y → x = 1 + y := by decide
  exact hs x y h

/-- Both reflection classes contain a translated binomial cube of degree at least N-4. -/
lemma reflection_cube (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) (eps : F) :
    ∃ j D : ℕ, j ≤ 2 ∧ N = D + 2 * j ∧ N ≤ D + 4 ∧
      ∀ z ∈ cube D, tm (j + z) + tm (N - (j + z)) = eps := by
  by_cases heps : eps = tm N
  · refine ⟨0, N, by omega, by omega, by omega, ?_⟩
    intro z hz
    simpa only [heps, Nat.zero_add, Nat.sub_zero] using cube_reflection N z hz
  have hopp : eps = 1 + tm N := f2_opposite eps (tm N) heps
  obtain ⟨v, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : N ≠ 0)
  have hvpos : 0 < v := by
    by_contra hn
    have hvzero : v = 0 := by omega
    rw [hvzero, pow_zero, Nat.one_mul] at hNm
    have hzero : (m : F) = 0 := by simpa only [hNm] using hEven.natCast_zmod_two
    exact zero_ne_one (hzero.symm.trans hm.natCast_zmod_two)
  rcases CharTwo.natCast_cases (R := F) v with hv | hv
  · have hvge : 2 ≤ v := by
      by_contra hn
      have hvone : v = 1 := by omega
      have hbad : (1 : F) = 0 := by simpa only [hvone, Nat.cast_one] using hv
      exact one_ne_zero hbad
    have hNdiv : 4 ∣ N := by
      rw [hNm]
      have hp : (2 : ℕ) ^ 2 ∣ 2 ^ v := pow_dvd_pow 2 hvge
      exact dvd_mul_of_dvd_left hp m
    have hNfour : 4 ≤ N := Nat.le_of_dvd (by omega) hNdiv
    have hDdiv : 2 ^ 2 ∣ N - 4 := Nat.dvd_sub hNdiv (dvd_refl 4)
    have hdiff : tm (N - 4) + tm N = 1 := by
      have h := tm_sub_power_difference v m 2 hm hvge
      have htwo : ((2 : ℕ) : F) = 0 := by decide
      have hpow : (2 : ℕ) ^ 2 = 4 := by decide
      simpa only [← hNm, hv, htwo, hpow, add_zero] using h
    have hpar : tm (N - 4) = eps :=
      ((CharTwo.add_eq_iff_eq_add).1 hdiff).trans hopp.symm
    refine ⟨2, N - 4, by omega, by omega, by omega, ?_⟩
    intro z hz
    rw [← hpar]
    exact shifted_cube_reflection 2 2 (N - 4) N z hDdiv (by decide) (by omega) hz
  · have hDdiv : 2 ^ 1 ∣ N - 2 := Nat.dvd_sub hEven.two_dvd (dvd_refl 2)
    have hdiff : tm (N - 2) + tm N = 1 := by
      have h := tm_sub_power_difference v m 1 hm hvpos
      have hone : (1 : F) + 1 + 1 = 1 := by decide
      simpa only [← hNm, hv, Nat.cast_one, hone, pow_one] using h
    have hpar : tm (N - 2) = eps :=
      ((CharTwo.add_eq_iff_eq_add).1 hdiff).trans hopp.symm
    refine ⟨1, N - 2, by omega, by omega, by omega, ?_⟩
    intro z hz
    rw [← hpar]
    exact shifted_cube_reflection 1 1 (N - 2) N z hDdiv (by decide) (by omega) hz

#print axioms reflection_cube
end TmClasses
```

### `TmProgression.lean`

```lean
import TmClasses

namespace TmProgression
open TmCore TmBinary TmCube TmReflection TmClasses

lemma forced_change (e d n r : ℕ)
    (hrem : n % (2 ^ e) = r) (hrd : r + d < 2 ^ e)
    (hletters : tm r ≠ tm (r + d)) : tm n ≠ tm (n + d) := by
  have hr : r < 2 ^ e := by omega
  have hn : n = 2 ^ e * (n / (2 ^ e)) + r := by
    have h := Nat.mod_add_div n (2 ^ e)
    omega
  have hnd : n + d = 2 ^ e * (n / (2 ^ e)) + (r + d) := by omega
  have hnword : tm n = tm (n / (2 ^ e)) + tm r := by
    calc
      _ = tm (2 ^ e * (n / (2 ^ e)) + r) := congrArg tm hn
      _ = _ := tm_dyadic_block e _ r hr
  have hndword : tm (n + d) = tm (n / (2 ^ e)) + tm (r + d) := by
    calc
      _ = tm (2 ^ e * (n / (2 ^ e)) + (r + d)) := congrArg tm hnd
      _ = _ := tm_dyadic_block e _ (r + d) hrd
  rw [hnword, hndword]
  exact fun h => hletters (add_left_cancel h)

lemma reflected_forced_change (e d c r : ℕ)
    (hB : d + c = 2 ^ e) (hr : r < c)
    (hclass : tm r + tm (c - 1 - r) = 1 + (e : F)) : tm r ≠ tm (r + d) := by
  have hidx : r + d = 2 ^ e - 1 - (c - 1 - r) := by omega
  have href : c - 1 - r < 2 ^ e := by omega
  have hword : tm (r + d) = (e : F) + tm (c - 1 - r) := by
    rw [hidx]
    exact tm_dyadic_complement e _ href
  intro hsame
  rw [hword] at hsame
  have hzero : (0 : F) = 1 := by
    have h := congrArg (fun x : F => x + (e : F)) hclass
    rw [hsame] at h
    have hl : ((e : F) + tm (c - 1 - r) + tm (c - 1 - r)) + (e : F) = 0 := by
      rw [CharTwo.add_cancel_right, CharTwo.add_self_eq_zero]
    have hr : (1 + (e : F)) + (e : F) = 1 := CharTwo.add_cancel_right _ _
    rw [hl, hr] at h
    exact h
  exact zero_ne_one hzero

lemma shifted_complement_arc (B L x : ℕ) (hL : 1 ≤ L) (hLB : L ≤ B)
    (hx : x < B) (havoid : L - 1 ≤ x) : (x + (B - L + 1)) % B ≤ B - L := by
  have hi : x + (B - L + 1) = (x - (L - 1)) + B := by omega
  have hsmall : x - (L - 1) < B := by omega
  rw [hi, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]
  omega

lemma cube_avoidance_bound (e D u a L : ℕ)
    (hD : D < 2 ^ e) (hcop : Nat.Coprime (2 ^ e) u)
    (hL : 1 ≤ L) (hLB : L ≤ 2 ^ e)
    (havoid : ∀ z ∈ cube D, L - 1 ≤ (a + u * z) % (2 ^ e)) : L + D ≤ 2 ^ e := by
  have hdeg : D ≤ 2 ^ e - L := by
    apply cube_compression e D u (a + (2 ^ e - L + 1)) (2 ^ e - L) hD hcop
    intro z hz
    have hidx : (a + (2 ^ e - L + 1) + u * z) % (2 ^ e) =
        ((a + u * z) % (2 ^ e) + (2 ^ e - L + 1)) % (2 ^ e) := by
      have hi : a + (2 ^ e - L + 1) + u * z = (a + u * z) + (2 ^ e - L + 1) := by omega
      rw [hi]
      simp only [Nat.add_mod, Nat.mod_mod]
    rw [hidx]
    exact shifted_complement_arc (2 ^ e) L _ hL hLB
      (Nat.mod_lt _ (pow_pos (by decide) e)) (havoid z hz)
  omega

#print axioms reflected_forced_change
#print axioms cube_avoidance_bound
end TmProgression
```

### `TmOrbit.lean`

```lean
import TmProgression

namespace TmOrbit
open TmCore TmBinary TmCube TmReflection TmClasses TmProgression

lemma orbit_coordinate (B d u a n r : ℕ)
    (hdu : (d : ZMod B) * (u : ZMod B) = 1)
    (ha : (a : ZMod B) = -(u : ZMod B) * (n : ZMod B)) (hr : r < B) :
    (n + ((a + u * r) % B) * d) % B = r := by
  have hi : (((a + u * r) % B : ℕ) : ZMod B) = (a : ZMod B) + (u : ZMod B) * (r : ZMod B) := by
    rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  have heq : ((n + ((a + u * r) % B) * d : ℕ) : ZMod B) = (r : ZMod B) := by
    rw [Nat.cast_add, Nat.cast_mul, hi]
    calc
      _ = (n : ZMod B) * (1 - (d : ZMod B) * (u : ZMod B)) +
          ((d : ZMod B) * (u : ZMod B)) * (r : ZMod B) := by rw [ha]; ring
      _ = _ := by rw [hdu]; simp
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ B).1 heq
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hmod

lemma mono_transition_ne_forced (e n d L i r : ℕ)
    (hmono : Mono n d L) (hi : i + 1 < L)
    (hrem : (n + i * d) % (2 ^ e) = r) (hrd : r + d < 2 ^ e)
    (hletters : tm r ≠ tm (r + d)) : False := by
  have hforced := forced_change e d (n + i * d) r hrem hrd hletters
  have hi0 : i < L := by omega
  have hidx : n + (i + 1) * d = (n + i * d) + d := by ring
  apply hforced
  rw [← hidx, hmono i hi0, hmono (i + 1) hi]

/-- A complete bound for every odd difference with a dyadic block at least d+3. -/
lemma odd_bound_in_block (e d c n L : ℕ)
    (hd : 0 < d) (hodd : Odd d) (hc : 3 ≤ c) (hB : d + c = 2 ^ e)
    (hmono : Mono n d L) : L ≤ d + 5 := by
  by_cases hLzero : L = 0
  · omega
  have hL : 1 ≤ L := by omega
  have he : 0 < e := by
    by_contra hn
    have hezero : e = 0 := by omega
    rw [hezero, pow_zero] at hB
    omega
  have hBpos : 0 < 2 ^ e := pow_pos (by decide) e
  let : NeZero (2 ^ e) := ⟨by omega⟩
  have hcop : Nat.Coprime d (2 ^ e) := hodd.coprime_two_right.pow_right e
  let u : ℕ := ((d : ZMod (2 ^ e))⁻¹).val
  let a : ℕ := (-(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e))).val
  have hdu : (d : ZMod (2 ^ e)) * (u : ZMod (2 ^ e)) = 1 := by
    simpa only [u, ZMod.natCast_zmod_val] using ZMod.coe_mul_inv_eq_one d hcop
  have ha : (a : ZMod (2 ^ e)) = -(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e)) :=
    ZMod.natCast_zmod_val _
  have hucop : Nat.Coprime (2 ^ e) u := by
    have hdu' : ((u * d : ℕ) : ZMod (2 ^ e)) = (1 : ℕ) := by
      simpa only [Nat.cast_mul, Nat.cast_one, mul_comm] using hdu
    exact (Nat.coprime_of_mul_modEq_one d ((ZMod.natCast_eq_natCast_iff _ _ (2 ^ e)).1 hdu')).symm
  have hcEven : Even (c - 1) := by
    have hdcast : (d : F) = 1 := hodd.natCast_zmod_two
    have hBcast : ((2 ^ e : ℕ) : F) = 0 := by
      rw [Nat.cast_pow]
      simp only [Nat.cast_ofNat, CharTwo.two_eq_zero (R := F), zero_pow he.ne']
    apply (ZMod.natCast_eq_zero_iff_even).1
    have hsum : d + (c - 1) + 1 = 2 ^ e := by omega
    have hsumcast := congrArg (fun x : ℕ => (x : F)) hsum
    rw [Nat.cast_add, Nat.cast_add, hdcast, Nat.cast_one, hBcast] at hsumcast
    have hc0 : (1 : F) + (c - 1 : ℕ) + 1 = (c - 1 : ℕ) := by
      calc
        _ = (c - 1 : ℕ) + ((1 : F) + 1) := by ring
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
    rwa [hc0] at hsumcast
  obtain ⟨j, D, hj, hN, hsize, hclass⟩ :=
    reflection_cube (c - 1) (by omega) hcEven (1 + (e : F))
  have hD : D < 2 ^ e := by omega
  have havoid : ∀ z ∈ cube D, L - 1 ≤ ((a + u * j) + u * z) % (2 ^ e) := by
    intro z hz
    have hzle := cube_mem_le D z hz
    have hr : j + z < c := by omega
    have hletters := reflected_forced_change e d c (j + z) hB hr (hclass z hz)
    have hcoord := orbit_coordinate (2 ^ e) d u a n (j + z) hdu ha (by omega)
    have hi_eq : a + u * (j + z) = (a + u * j) + u * z := by ring
    rw [hi_eq] at hcoord
    by_contra hn
    have hi : ((a + u * j) + u * z) % (2 ^ e) + 1 < L := by omega
    exact mono_transition_ne_forced e n d L _ (j + z) hmono hi hcoord (by omega) hletters
  have hLB : L ≤ 2 ^ e := by
    obtain ⟨z, hz⟩ := cube_nonempty D
    have hidx := havoid z hz
    have hi : ((a + u * j) + u * z) % (2 ^ e) < 2 ^ e := Nat.mod_lt _ hBpos
    omega
  have hLD := cube_avoidance_bound e D u (a + u * j) L hD hucop hL hLB havoid
  omega

lemma odd_progression_bound (d n L : ℕ) (hd : 0 < d) (hodd : Odd d)
    (hmono : Mono n d L) : L ≤ d + 5 := by
  have hp : d + 3 < 2 ^ (d + 3) := (d + 3).lt_two_pow_self
  exact odd_bound_in_block (d + 3) d (2 ^ (d + 3) - d) n L hd hodd
    (by omega) (by omega) hmono

/-- The upper-bound half of Sobolewski's Conjecture 3, for the actual Thue-Morse word. -/
theorem thueMorse_progression_bound (d n L : ℕ) (hd : 0 < d)
    (hmono : Mono n d L) : L ≤ d + 5 := by
  induction d using Nat.strong_induction_on generalizing n L with
  | h d ih =>
    rcases Nat.even_or_odd d with heven | hodd
    · obtain ⟨k, hk⟩ := heven
      have hdk : d = 2 * k := by omega
      have hkpos : 0 < k := by omega
      have hklt : k < d := by omega
      have hmono' : Mono (n / 2) k L := by
        apply (mono_double_iff n k L).1
        simpa only [hdk] using hmono
      have hb := ih k hklt (n / 2) L hkpos hmono'
      omega
    · exact odd_progression_bound d n L hd hodd hmono

#print axioms thueMorse_progression_bound

#print axioms odd_bound_in_block
end TmOrbit
```

### `TmQuantitative.lean`

```lean
import TmOrbit

namespace TmQuantitative
open TmCore TmBinary TmCube TmReflection TmClasses TmProgression TmOrbit

lemma bound_from_cube (e d c n L j D : ℕ)
    (hd : 0 < d) (hodd : Odd d) (hc : 3 ≤ c) (hB : d + c = 2 ^ e)
    (hN : c - 1 = D + 2 * j)
    (hclass : ∀ z ∈ cube D, tm (j + z) + tm (c - 1 - (j + z)) = 1 + (e : F))
    (hmono : Mono n d L) : L + D ≤ 2 ^ e := by
  have hD : D < 2 ^ e := by omega
  by_cases hLzero : L = 0
  · omega
  have hL : 1 ≤ L := by omega
  have he : 0 < e := by
    by_contra hn
    have hezero : e = 0 := by omega
    rw [hezero, pow_zero] at hB
    omega
  have hBpos : 0 < 2 ^ e := pow_pos (by decide) e
  let : NeZero (2 ^ e) := ⟨by omega⟩
  have hcop : Nat.Coprime d (2 ^ e) := hodd.coprime_two_right.pow_right e
  let u : ℕ := ((d : ZMod (2 ^ e))⁻¹).val
  let a : ℕ := (-(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e))).val
  have hdu : (d : ZMod (2 ^ e)) * (u : ZMod (2 ^ e)) = 1 := by
    simpa only [u, ZMod.natCast_zmod_val] using ZMod.coe_mul_inv_eq_one d hcop
  have ha : (a : ZMod (2 ^ e)) = -(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e)) :=
    ZMod.natCast_zmod_val _
  have hucop : Nat.Coprime (2 ^ e) u := by
    have hdu' : ((u * d : ℕ) : ZMod (2 ^ e)) = (1 : ℕ) := by
      simpa only [Nat.cast_mul, Nat.cast_one, mul_comm] using hdu
    exact (Nat.coprime_of_mul_modEq_one d ((ZMod.natCast_eq_natCast_iff _ _ (2 ^ e)).1 hdu')).symm
  have havoid : ∀ z ∈ cube D, L - 1 ≤ ((a + u * j) + u * z) % (2 ^ e) := by
    intro z hz
    have hzle := cube_mem_le D z hz
    have hr : j + z < c := by omega
    have hletters := reflected_forced_change e d c (j + z) hB hr (hclass z hz)
    have hcoord := orbit_coordinate (2 ^ e) d u a n (j + z) hdu ha (by omega)
    have hi_eq : a + u * (j + z) = (a + u * j) + u * z := by ring
    rw [hi_eq] at hcoord
    by_contra hn
    have hi : ((a + u * j) + u * z) % (2 ^ e) + 1 < L := by omega
    exact mono_transition_ne_forced e n d L _ (j + z) hmono hi hcoord (by omega) hletters
  have hLB : L ≤ 2 ^ e := by
    obtain ⟨z, hz⟩ := cube_nonempty D
    have hidx := havoid z hz
    have hi : ((a + u * j) + u * z) % (2 ^ e) < 2 ^ e := Nat.mod_lt _ hBpos
    omega
  have hLD := cube_avoidance_bound e D u (a + u * j) L hD hucop hL hLB havoid
  exact hLD

#print axioms bound_from_cube
end TmQuantitative
```

### `TmFrobenius.lean`

```lean
import TmClasses

open Polynomial
namespace TmFrobenius
open TmCore TmCube TmCyclic TmReflection TmValuation

lemma y_div_iff (K : ℕ) (P : R) (hP : P ≠ 0) :
    (X + 1 : R) ^ K ∣ P ↔ K ≤ P.rootMultiplicity (1 : F) := by
  have hy : (X - C (1 : F) : R) = X + 1 := by rw [map_one, CharTwo.sub_eq_add]
  simpa only [hy] using (le_rootMultiplicity_iff hP (a := (1 : F)) (n := K)).symm

lemma y_rootMultiplicity (D : ℕ) : ((X + 1 : R) ^ D).rootMultiplicity (1 : F) = D := by
  have hy : (X + 1 : R).rootMultiplicity (1 : F) = 1 := by
    simpa only [add_comm, pow_one] using odd_binomial_rootMultiplicity 1 (by decide) (by decide)
  rw [rootMultiplicity_pow_local _ x_plus_one_ne_zero D, hy, Nat.mul_one]

lemma monomial_y_rootMultiplicity (a D : ℕ) :
    (X ^ a * (X + 1) ^ D : R).rootMultiplicity (1 : F) = D := by
  have hP : (X ^ a * (X + 1) ^ D : R) ≠ 0 :=
    mul_ne_zero (pow_ne_zero a X_ne_zero) (pow_ne_zero D x_plus_one_ne_zero)
  rw [rootMultiplicity_mul hP, monomial_rootMultiplicity, y_rootMultiplicity, Nat.zero_add]

lemma square_cancel_y (M : ℕ) (P : R)
    (h : (X + 1 : R) ^ (2 * M) ∣ P ^ 2) : (X + 1 : R) ^ M ∣ P := by
  by_cases hP : P = 0
  · rw [hP]; exact dvd_zero _
  apply (y_div_iff M P hP).2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero 2 hP
  have hm := (y_div_iff (2 * M) (P ^ 2) hP2).1 h
  rw [rootMultiplicity_pow_local P hP 2] at hm
  omega

lemma euler_even_product (a D : ℕ) (hD : (D : F) = 0) :
    X * derivative ((X : R) ^ a * (X + 1) ^ D) = C (a : F) * X ^ a * (X + 1) ^ D := by
  rw [derivative_mul, mul_add]
  have hid : (X : R) * (derivative (X ^ a) * (X + 1) ^ D) =
      (X * derivative (X ^ a)) * (X + 1) ^ D := by ring
  rw [hid, euler_monomial, derivative_pow, hD, map_zero]
  simp

lemma congruence_even_translation (M D u a : ℕ)
    (hM : (M : F) = 0) (hD : (D : F) = 0) (hsmall : D < M)
    (h : (X + 1 : R) ^ M ∣ (1 + X ^ u) ^ D - X ^ a * (X + 1) ^ D) : Even a := by
  apply ZMod.natCast_eq_zero_iff_even.1
  rcases CharTwo.natCast_cases (R := F) a with ha | ha
  · exact ha
  · have hd := derivative_preserves_modulus M hM _ h
    have hx := dvd_mul_of_dvd_right hd (X : R)
    have hp : (X : R) * derivative ((1 + X ^ u : R) ^ D) = 0 := by
      rw [euler_derivative_pow, hD, map_zero, zero_mul, zero_mul]
    rw [euler_derivative_sub, hp, euler_even_product a D hD, ha, map_one, one_mul,
      zero_sub] at hx
    have hx' : (X + 1 : R) ^ M ∣ X ^ a * (X + 1) ^ D := dvd_neg.mp hx
    have hP : (X ^ a * (X + 1) ^ D : R) ≠ 0 :=
      mul_ne_zero (pow_ne_zero a X_ne_zero) (pow_ne_zero D x_plus_one_ne_zero)
    have hbound := (y_div_iff M _ hP).1 hx'
    rw [monomial_y_rootMultiplicity] at hbound
    omega

lemma square_congruence_descend (e K u b : ℕ)
    (h : (X + 1 : R) ^ (2 ^ (e + 1)) ∣
      (1 + X ^ u) ^ (2 * K) - X ^ (2 * b) * (X + 1) ^ (2 * K)) :
    (X + 1 : R) ^ (2 ^ e) ∣ (1 + X ^ u) ^ K - X ^ b * (X + 1) ^ K := by
  apply square_cancel_y (2 ^ e)
  have hid : ((1 + X ^ u) ^ K - X ^ b * (X + 1) ^ K : R) ^ 2 =
      (1 + X ^ u) ^ (2 * K) - X ^ (2 * b) * (X + 1) ^ (2 * K) := by
    simp only [CharTwo.sub_eq_add, CharTwo.add_sq, mul_pow, ← pow_mul, Nat.mul_comm]
  rw [hid]
  have heq : 2 * 2 ^ e = 2 ^ (e + 1) := by rw [pow_succ, Nat.mul_comm]
  rwa [heq]

lemma dyadic_cast_zero (e : ℕ) (he : 0 < e) : ((2 ^ e : ℕ) : F) = 0 := by
  rw [Nat.cast_pow]
  have htwo : ((2 : ℕ) : F) = 0 := by decide
  rw [htwo, zero_pow he.ne']

/-- Removing trailing zero bits is forced by the congruence itself. -/
lemma affine_congruence_deflate (v s E u a : ℕ) (hsmall : E < 2 ^ s)
    (h : (X + 1 : R) ^ (2 ^ (v + s)) ∣
      (1 + X ^ u) ^ (2 ^ v * E) - X ^ a * (X + 1) ^ (2 ^ v * E)) :
    ∃ b : ℕ, a = 2 ^ v * b ∧
      (X + 1 : R) ^ (2 ^ s) ∣ (1 + X ^ u) ^ E - X ^ b * (X + 1) ^ E := by
  induction v generalizing a with
  | zero =>
    refine ⟨a, by simp, ?_⟩
    simpa only [Nat.zero_add, pow_zero, Nat.one_mul] using h
  | succ v ih =>
    have hExp : v + 1 + s = (v + s) + 1 := by omega
    have hD : 2 ^ (v + 1) * E = 2 * (2 ^ v * E) := by rw [pow_succ]; ring
    have hMcast : ((2 ^ (v + 1 + s) : ℕ) : F) = 0 := dyadic_cast_zero _ (by omega)
    have hDcast : ((2 ^ (v + 1) * E : ℕ) : F) = 0 := by
      rw [hD, Nat.cast_mul]
      have htwo : ((2 : ℕ) : F) = 0 := by decide
      rw [htwo, zero_mul]
    have hDsmall : 2 ^ (v + 1) * E < 2 ^ (v + 1 + s) := by
      rw [pow_add 2 (v + 1) s]
      exact Nat.mul_lt_mul_of_pos_left hsmall (pow_pos (by decide : 0 < 2) (v + 1))
    have haEven := congruence_even_translation _ _ u a hMcast hDcast hDsmall h
    obtain ⟨b, hb⟩ := haEven
    have hab : a = 2 * b := by omega
    have h' : (X + 1 : R) ^ (2 ^ (v + s)) ∣
        (1 + X ^ u) ^ (2 ^ v * E) - X ^ b * (X + 1) ^ (2 ^ v * E) := by
      apply square_congruence_descend (v + s) (2 ^ v * E) u b
      simpa only [hExp, hD, hab] using h
    obtain ⟨c, hc, hfinal⟩ := ih b h'
    refine ⟨c, ?_, hfinal⟩
    rw [hab, hc, pow_succ]
    ring

#print axioms affine_congruence_deflate

#print axioms congruence_even_translation
#print axioms square_congruence_descend
end TmFrobenius
```

### `TmRigidity.lean`

```lean
import TmFrobenius

open Polynomial
namespace TmRigidity
open TmCore TmCube TmCyclic TmReflection TmFrobenius

lemma reduce_exponent_congruence (s E u a : ℕ)
    (h : (X + 1 : R) ^ (2 ^ s) ∣ (1 + X ^ u) ^ E - X ^ a * (X + 1) ^ E) :
    (X + 1 : R) ^ (2 ^ s) ∣ (1 + X ^ (u % (2 ^ s))) ^ E - X ^ a * (X + 1) ^ E := by
  have hm := monomial_reduction s u
  have hb : (X + 1 : R) ^ (2 ^ s) ∣ (1 + X ^ u) - (1 + X ^ (u % (2 ^ s))) := by
    have hi : (1 + X ^ u : R) - (1 + X ^ (u % (2 ^ s))) = X ^ u - X ^ (u % (2 ^ s)) := by ring
    rwa [hi]
  have hp := hb.trans (sub_dvd_pow_sub_pow (1 + X ^ u : R) (1 + X ^ (u % (2 ^ s))) E)
  have hr := dvd_sub h hp
  have hi : ((1 + X ^ u) ^ E - X ^ a * (X + 1) ^ E : R) -
      ((1 + X ^ u) ^ E - (1 + X ^ (u % (2 ^ s))) ^ E) =
      (1 + X ^ (u % (2 ^ s))) ^ E - X ^ a * (X + 1) ^ E := by ring
  rwa [hi] at hr

lemma odd_mod_dyadic_cast (s u : ℕ) (hs : 0 < s) (hu : Odd u) :
    ((u % (2 ^ s) : ℕ) : F) = 1 := by
  have hdiv : 2 ∣ 2 ^ s := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
    refine ⟨2 ^ t, ?_⟩
    rw [ht, pow_succ, Nat.mul_comm]
  have hm := Nat.mod_mod_of_dvd u hdiv
  have hc := congrArg (fun x : ℕ => (x : F)) hm
  simp only [ZMod.natCast_mod] at hc
  exact hc.trans hu.natCast_zmod_two

lemma primitive_rigidity_mod (s E u a : ℕ)
    (hs : 0 < s) (hEpos : 1 ≤ E) (hsmall : 2 * E < 2 ^ s)
    (hE : Odd E) (hu : Odd u)
    (h : (X + 1 : R) ^ (2 ^ s) ∣ (1 + X ^ u) ^ E - X ^ a * (X + 1) ^ E) :
    u % (2 ^ s) = 1 ∨ u % (2 ^ s) + 1 = 2 ^ s := by
  have hc := odd_mod_dyadic_cast s u hs hu
  have hpos : 1 ≤ u % (2 ^ s) := by
    by_contra hn
    have hz : u % (2 ^ s) = 0 := by omega
    have hzero : (0 : F) = 1 := by simpa only [hz, Nat.cast_zero] using hc
    exact zero_ne_one hzero
  exact primitive_affine_rigidity s E (u % (2 ^ s)) a hs hEpos hsmall hpos
    (Nat.mod_lt _ (pow_pos (by decide) s)) hE.natCast_zmod_two hc
    (reduce_exponent_congruence s E u a h)

/-- General affine binomial rigidity after removal of all trailing-zero bits. -/
theorem affine_binomial_rigidity (v s E u a : ℕ)
    (hEpos : 1 ≤ E) (hsmall : 2 * E < 2 ^ s) (hE : Odd E) (hu : Odd u)
    (h : (X + 1 : R) ^ (2 ^ (v + s)) ∣
      (1 + X ^ u) ^ (2 ^ v * E) - X ^ a * (X + 1) ^ (2 ^ v * E)) :
    u % (2 ^ s) = 1 ∨ u % (2 ^ s) + 1 = 2 ^ s := by
  have hs : 0 < s := by
    by_contra hn
    have hz : s = 0 := by omega
    rw [hz, pow_zero] at hsmall
    omega
  obtain ⟨b, _, hb⟩ := affine_congruence_deflate v s E u a (by omega) h
  exact primitive_rigidity_mod s E u b hs hEpos hsmall hE hu hb

#print axioms affine_binomial_rigidity
end TmRigidity
```

### `TmEquality.lean`

```lean
import TmRigidity

open Polynomial
open scoped BigOperators
namespace TmEquality
open TmCore TmCube TmCyclic TmFrobenius TmRigidity

lemma compression_equality (e D u a : ℕ)
    (hD : D < 2 ^ e) (hcop : Nat.Coprime (2 ^ e) u)
    (harc : ∀ z ∈ cube D, (a + u * z) % (2 ^ e) ≤ D) :
    (X + 1 : R) ^ (2 ^ e) ∣ X ^ a * (1 + X ^ u) ^ D - (X + 1) ^ D := by
  let Q : R := ∑ z ∈ cube D, X ^ ((a + u * z) % (2 ^ e))
  have hQ : Q ≠ 0 := indicator_nonzero (cube D) _ (cube_nonempty D)
    (affine_reduction_injective (2 ^ e) u a (cube D) hcop
      (fun z hz => (cube_mem_le D z hz).trans_lt hD))
  have hdeg : Q.natDegree ≤ D := indicator_degree (cube D) _ D harc
  have hmod := reduction_sum e (cube D) (fun z => a + u * z)
  rw [cube_generating] at hmod
  have hp : (X + 1 : R) ^ D ∣ X ^ a * (1 + X ^ u) ^ D :=
    dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (linear_factor_dvd u) D) _
  have hdiff : (X + 1 : R) ^ D ∣ Q - X ^ a * (1 + X ^ u) ^ D := by
    have hb : (X + 1 : R) ^ D ∣ (X + 1) ^ (2 ^ e) := pow_dvd_pow _ hD.le
    simpa only [neg_sub] using dvd_neg.mpr (hb.trans hmod)
  have hdiv : (X + 1 : R) ^ D ∣ Q := by
    have hh := dvd_add hdiff hp
    simpa using hh
  have hqmonic : Q.Monic := by
    apply f2_eq_one_of_ne_zero
    exact leadingCoeff_ne_zero.mpr hQ
  have hpmonic : ((X + 1 : R) ^ D).Monic := by
    simpa only [map_one] using (monic_X_add_C (1 : F)).pow D
  have hpdeg : ((X + 1 : R) ^ D).natDegree = D := by
    simpa only [map_one] using natDegree_pow_X_add_C D (1 : F)
  have hQeq : Q = (X + 1 : R) ^ D :=
    eq_of_monic_of_dvd_of_natDegree_le hpmonic hqmonic hdiv (by rwa [hpdeg])
  change (X + 1 : R) ^ (2 ^ e) ∣ X ^ a * (1 + X ^ u) ^ D - Q at hmod
  rwa [hQeq] at hmod

lemma move_monomial_congruence (e a : ℕ) (P Q : R)
    (h : (X + 1 : R) ^ (2 ^ e) ∣ X ^ a * P - Q) :
    ∃ b : ℕ, (X + 1 : R) ^ (2 ^ e) ∣ P - X ^ b * Q := by
  let b := 2 ^ e - a % (2 ^ e)
  have hsmall : a % (2 ^ e) < 2 ^ e := Nat.mod_lt _ (pow_pos (by decide) e)
  have hab : a % (2 ^ e) + b = 2 ^ e := by dsimp [b]; omega
  have hmod : (a + b) % (2 ^ e) = 0 := by
    calc
      _ = (a % (2 ^ e) + b) % (2 ^ e) := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = 0 := by rw [hab, Nat.mod_self]
  have hmono : (X + 1 : R) ^ (2 ^ e) ∣ X ^ (a + b) - 1 := by
    simpa only [hmod, pow_zero] using monomial_reduction e (a + b)
  have hp := dvd_mul_of_dvd_right h (X ^ b : R)
  have hq := dvd_mul_of_dvd_right hmono P
  have hr := dvd_sub hp hq
  have hid : (X ^ b * (X ^ a * P - Q) - P * (X ^ (a + b) - 1) : R) = P - X ^ b * Q := by
    rw [pow_add]
    ring
  refine ⟨b, ?_⟩
  rwa [hid] at hr

/-- The full algebraic equality obstruction used in the ordinary proof. -/
theorem compressed_cube_rigidity (v s E u a : ℕ)
    (hEpos : 1 ≤ E) (hsmall : 2 * E < 2 ^ s) (hE : Odd E) (hu : Odd u)
    (hcop : Nat.Coprime (2 ^ (v + s)) u)
    (harc : ∀ z ∈ cube (2 ^ v * E), (a + u * z) % (2 ^ (v + s)) ≤ 2 ^ v * E) :
    u % (2 ^ s) = 1 ∨ u % (2 ^ s) + 1 = 2 ^ s := by
  have hD : 2 ^ v * E < 2 ^ (v + s) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left (by omega : E < 2 ^ s) (pow_pos (by decide : 0 < 2) v)
  have hcomp := compression_equality (v + s) (2 ^ v * E) u a hD hcop harc
  obtain ⟨b, hb⟩ := move_monomial_congruence (v + s) a _ _ hcomp
  exact affine_binomial_rigidity v s E u b hEpos hsmall hE hu hb

#print axioms compressed_cube_rigidity
end TmEquality
```

### `TmArcBridge.lean`

```lean
import TmQuantitative
import TmEquality

namespace TmArcBridge
open TmCore TmBinary TmCube TmReflection TmClasses TmProgression TmOrbit

lemma forced_set_arc (e d c n L j D : ℕ)
    (hd : 0 < d) (hodd : Odd d) (hc : 3 ≤ c) (hB : d + c = 2 ^ e)
    (hN : c - 1 = D + 2 * j)
    (hclass : ∀ z ∈ cube D, tm (j + z) + tm (c - 1 - (j + z)) = 1 + (e : F))
    (hL : 1 ≤ L) (hmono : Mono n d L) :
    ∃ u a : ℕ, u < 2 ^ e ∧ Odd u ∧ Nat.Coprime (2 ^ e) u ∧
      d * u ≡ 1 [MOD 2 ^ e] ∧ L ≤ 2 ^ e ∧
      (a : ZMod (2 ^ e)) = -(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e)) +
        ((2 ^ e - L + 1 : ℕ) : ZMod (2 ^ e)) ∧
      ∀ r < c, tm r + tm (c - 1 - r) = 1 + (e : F) →
        (a + u * r) % (2 ^ e) ≤ 2 ^ e - L := by
  have he : 0 < e := by
    by_contra hn
    have hezero : e = 0 := by omega
    rw [hezero, pow_zero] at hB
    omega
  have hBpos : 0 < 2 ^ e := pow_pos (by decide) e
  let : NeZero (2 ^ e) := ⟨by omega⟩
  have hcop : Nat.Coprime d (2 ^ e) := hodd.coprime_two_right.pow_right e
  let u : ℕ := ((d : ZMod (2 ^ e))⁻¹).val
  let a : ℕ := (-(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e))).val
  have hdu : (d : ZMod (2 ^ e)) * (u : ZMod (2 ^ e)) = 1 := by
    simpa only [u, ZMod.natCast_zmod_val] using ZMod.coe_mul_inv_eq_one d hcop
  have ha : (a : ZMod (2 ^ e)) = -(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e)) :=
    ZMod.natCast_zmod_val _
  have hdumod : d * u ≡ 1 [MOD 2 ^ e] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ (2 ^ e)).1
    simpa only [Nat.cast_mul, Nat.cast_one] using hdu
  have hucop : Nat.Coprime (2 ^ e) u := by
    have humod : u * d ≡ 1 [MOD 2 ^ e] := by simpa only [Nat.mul_comm] using hdumod
    exact (Nat.coprime_of_mul_modEq_one d humod).symm
  have htwo : 2 ∣ 2 ^ e := by
    obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    refine ⟨2 ^ f, ?_⟩
    rw [hf, pow_succ, Nat.mul_comm]
  have huodd : Odd u := Nat.coprime_two_left.1 (Nat.Coprime.of_dvd_left htwo hucop)
  have havoid : ∀ r < c, tm r + tm (c - 1 - r) = 1 + (e : F) →
      L - 1 ≤ (a + u * r) % (2 ^ e) := by
    intro r hr hletters
    have hcoord := orbit_coordinate (2 ^ e) d u a n r hdu ha (by omega)
    by_contra hn
    have hi : (a + u * r) % (2 ^ e) + 1 < L := by omega
    exact mono_transition_ne_forced e n d L _ r hmono hi hcoord (by omega)
      (reflected_forced_change e d c r hB hr hletters)
  have hLB : L ≤ 2 ^ e := by
    obtain ⟨z, hz⟩ := cube_nonempty D
    have hzle := cube_mem_le D z hz
    have hr : j + z < c := by omega
    have hidx := havoid (j + z) hr (hclass z hz)
    have hi : (a + u * (j + z)) % (2 ^ e) < 2 ^ e := Nat.mod_lt _ hBpos
    omega
  refine ⟨u, a + (2 ^ e - L + 1), ZMod.val_lt _, huodd, hucop, hdumod, hLB, ?_, ?_⟩
  · rw [Nat.cast_add, ha]
  · intro r hr hletters
    have hidx : (a + (2 ^ e - L + 1) + u * r) % (2 ^ e) =
        ((a + u * r) % (2 ^ e) + (2 ^ e - L + 1)) % (2 ^ e) := by
      have hi : a + (2 ^ e - L + 1) + u * r = (a + u * r) + (2 ^ e - L + 1) := by omega
      rw [hi]
      simp only [Nat.add_mod, Nat.mod_mod]
    rw [hidx]
    exact shifted_complement_arc (2 ^ e) L _ hL hLB (Nat.mod_lt _ hBpos) (havoid r hr hletters)

#print axioms forced_set_arc
end TmArcBridge
```

### `TmAttainment.lean`

```lean
import TmOrbit
import Mathlib.Tactic.Linarith

namespace TmAttainment
open TmCore TmBinary TmCube TmReflection TmValuation TmOrbit

@[simp] lemma tm_one : tm 1 = 1 := by decide
@[simp] lemma tm_two : tm 2 = 1 := by decide
@[simp] lemma tm_three : tm 3 = 0 := by decide
@[simp] lemma tm_four : tm 4 = 1 := by decide

lemma progression_pair (B m r i q s : ℕ) (hB : 1 ≤ B)
    (hp : B * q + s + i = B * (m + i) + r) :
    B * m + r + i * (B - 1) = B * q + s := by
  have hi : i * (B - 1) + i = i * B := by
    calc
      _ = i * ((B - 1) + 1) := by ring
      _ = i * B := by rw [Nat.sub_add_cancel hB]
  nlinarith only [hi, hp]

/-- The known equality family, with a literal start and every letter verified. -/
theorem mersenne_attainment (e : ℕ) (he : 2 ≤ e) (hEven : Even e) :
    ∃ n : ℕ, Mono n (2 ^ e - 1) (2 ^ e + 4) := by
  let B := 2 ^ e
  have hB : 4 ≤ B := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) he
    exact h
  have hB1 : 1 ≤ B := by omega
  have hBpred : B - 1 + 1 = B := by omega
  have hBpred2 : B - 2 + 2 = B := by omega
  have hecast : (e : F) = 0 := hEven.natCast_zmod_two
  have hlo : tm (B - 1) = 0 := by
    exact (tm_mersenne e).trans hecast
  have hmidx : 3 * B - 1 = B * 2 + (B - 1) := by omega
  have hmword : tm (3 * B - 1) = 1 := by
    rw [hmidx, tm_dyadic_block e 2 (B - 1) (by omega), tm_two, hlo, add_zero]
  have hq3 : tm (3 * B) = 0 := by
    have hi : 3 * B = B * 3 := by ring
    rw [hi, tm_scale, tm_three]
  have hq4 : tm (4 * B) = 1 := by
    have hi : 4 * B = B * 4 := by ring
    rw [hi, tm_scale, tm_four]
  have hq4pred : tm (4 * B - 1) = 0 := by
    have hi : 4 * B - 1 = B * 3 + (B - 1) := by omega
    rw [hi, tm_dyadic_block e 3 (B - 1) (by omega), tm_three, hlo, zero_add]
  have hlo2 : tm (B - 2) = 1 := by
    have hi : B - 2 = B - 1 - 1 := by omega
    rw [hi, tm_dyadic_complement e 1 (by omega), hecast, zero_add, tm_one]
  let m := 3 * B - 1
  let n := B * m + 1
  have hm : m + 1 = 3 * B := by dsimp [m]; omega
  have hBm : B * m + B = 3 * B ^ 2 := by nlinarith [congrArg (fun x : ℕ => B * x) hm]
  have hstart : tm n = 0 := by
    change tm (B * m + 1) = 0
    rw [tm_dyadic_block e m 1 (by omega), hmword, tm_one]
    decide
  refine ⟨n, ?_⟩
  intro i hi
  rw [hstart]
  change tm (B * m + 1 + i * (B - 1)) = 0
  by_cases hi0 : i = 0
  · subst i
    simpa only [Nat.zero_mul, Nat.add_zero] using hstart
  by_cases hi1 : i = 1
  · subst i
    have hp : B * (3 * B) + 0 + 1 = B * (m + 1) + 1 := by rw [hm]
    rw [progression_pair B m 1 1 (3 * B) 0 hB1 hp,
      tm_dyadic_block e (3 * B) 0 (by omega), tm_zero, add_zero, hq3]
  by_cases himid : i < B + 2
  · let a := i - 2
    have ha : a < B := by dsimp [a]; omega
    have hia : i = 2 + a := by dsimp [a]; omega
    have hs : (B - 1 - a) + a + 1 = B := by omega
    have hp : B * (3 * B + a) + (B - 1 - a) + i = B * (m + i) + 1 := by
      rw [hia]
      nlinarith only [hBm, hs]
    rw [progression_pair B m 1 i (3 * B + a) (B - 1 - a) hB1 hp,
      tm_dyadic_block e (3 * B + a) (B - 1 - a) (by omega)]
    have hquot : tm (3 * B + a) = tm a := by
      have hidx : 3 * B + a = B * 3 + a := by ring
      rw [hidx, tm_dyadic_block e 3 a ha, tm_three, zero_add]
    rw [hquot, tm_dyadic_complement e a ha, hecast, zero_add]
    exact CharTwo.add_self_eq_zero _
  have hlast : i = B + 2 ∨ i = B + 3 := by change i < B + 4 at hi; omega
  rcases hlast with rfl | rfl
  · have hq : (4 * B - 1) + 1 = 4 * B := by omega
    have hBq : B * (4 * B - 1) + B = 4 * B ^ 2 := by
      nlinarith [congrArg (fun x : ℕ => B * x) hq]
    have hp : B * (4 * B - 1) + (B - 1) + (B + 2) = B * (m + (B + 2)) + 1 := by
      nlinarith only [hBm, hBq, hBpred]
    rw [progression_pair B m 1 (B + 2) (4 * B - 1) (B - 1) hB1 hp,
      tm_dyadic_block e (4 * B - 1) (B - 1) (by omega), hq4pred, hlo, zero_add]
  · have hp : B * (4 * B) + (B - 2) + (B + 3) = B * (m + (B + 3)) + 1 := by
      nlinarith only [hBm, hBpred2]
    rw [progression_pair B m 1 (B + 3) (4 * B) (B - 2) hB1 hp,
      tm_dyadic_block e (4 * B) (B - 2) (by omega), hq4, hlo2]
    decide

#print axioms mersenne_attainment
end TmAttainment
```

### `TmKnownCases.lean`

```lean
import TmAttainment
import TmQuantitative
import TmFrobenius

namespace TmKnownCases
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmOrbit TmAttainment TmQuantitative

lemma even_no_attainment (d n : ℕ) (hd : 0 < d) (heven : Even d) :
    ¬ Mono n d (d + 5) := by
  intro hmono
  obtain ⟨k, hk⟩ := heven
  have hdk : d = 2 * k := by omega
  have hkpos : 0 < k := by omega
  have hm : Mono (n / 2) k (d + 5) := by
    apply (mono_double_iff n k (d + 5)).1
    simpa only [hdk] using hmono
  have hb := thueMorse_progression_bound k (n / 2) (d + 5) hkpos hm
  omega

lemma one_no_attainment (n : ℕ) : ¬ Mono n 1 6 := by
  intro hmono
  apply tm_no_triple n
  have h1 := hmono 1 (by decide)
  have h2 := hmono 2 (by decide)
  simp only [Nat.mul_one] at h1 h2
  exact ⟨h1.symm, h1.trans h2.symm⟩

lemma mersenne_odd_bound (e n L : ℕ) (hodd : Odd e)
    (hmono : Mono n (2 ^ e - 1) L) : L ≤ 2 ^ e := by
  have hepos : 0 < e := by obtain ⟨k, hk⟩ := hodd; omega
  let B := 2 ^ e
  have hBtwo : 2 ≤ B := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hepos
    exact h
  have hBeven : Even B := (ZMod.natCast_eq_zero_iff_even).1 (dyadic_cast_zero e hepos)
  have hdodd : Odd (B - 1) := Nat.Even.sub_odd (by omega) hBeven (by decide)
  have hecast : (e : F) = 1 := hodd.natCast_zmod_two
  have heplus : ((e + 1 : ℕ) : F) = 0 := by
    rw [Nat.cast_add, hecast, Nat.cast_one]
    decide
  have hBword : tm B = 1 := by
    simpa only [Nat.mul_one, tm_one] using tm_scale e 1
  have hpow : 2 ^ (e + 1) = 2 * B := by rw [pow_succ]; ring
  have hclass : ∀ z ∈ cube B, tm (0 + z) + tm (B + 1 - 1 - (0 + z)) =
      1 + ((e + 1 : ℕ) : F) := by
    intro z hz
    simpa only [Nat.zero_add, Nat.add_sub_cancel, hBword, heplus, add_zero] using cube_reflection B z hz
  have hb := bound_from_cube (e + 1) (B - 1) (B + 1) n L 0 B
    (by omega) hdodd (by omega) (by omega) (by omega) hclass hmono
  rw [hpow] at hb
  omega

theorem mersenne_attainment_iff (e : ℕ) (he : 0 < e) :
    (∃ n : ℕ, Mono n (2 ^ e - 1) (2 ^ e + 4)) ↔ Even e ∧ 2 ≤ e := by
  constructor
  · rintro ⟨n, hn⟩
    rcases Nat.even_or_odd e with heven | hodd
    · refine ⟨heven, ?_⟩
      obtain ⟨k, hk⟩ := heven
      omega
    · have hb := mersenne_odd_bound e n (2 ^ e + 4) hodd hn
      omega
  · rintro ⟨heven, he2⟩
    exact mersenne_attainment e he2 heven

#print axioms mersenne_attainment_iff
#print axioms even_no_attainment
end TmKnownCases
```

### `TmConfiguration.lean`

```lean
import TmArcBridge
import TmKnownCases

namespace TmConfiguration
open TmCore TmBinary TmCube TmReflection TmValuation TmClasses TmFrobenius TmOrbit TmQuantitative

lemma reflection_index_even (e d c : ℕ) (he : 0 < e) (hodd : Odd d)
    (hc : 1 ≤ c) (hB : d + c = 2 ^ e) : Even (c - 1) := by
  have hdcast : (d : F) = 1 := hodd.natCast_zmod_two
  have hBcast := dyadic_cast_zero e he
  apply ZMod.natCast_eq_zero_iff_even.1
  have hsum : d + (c - 1) + 1 = 2 ^ e := by omega
  have h := congrArg (fun x : ℕ => (x : F)) hsum
  rw [Nat.cast_add, Nat.cast_add, hdcast, Nat.cast_one, hBcast] at h
  have hh : (1 : F) + ((c - 1 : ℕ) : F) + 1 = ((c - 1 : ℕ) : F) := by
    calc
      _ = ((c - 1 : ℕ) : F) + ((1 : F) + 1) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  rwa [hh] at h

lemma equality_parameters (e d c n : ℕ)
    (hd : 0 < d) (hodd : Odd d) (hc : 3 ≤ c) (hB : d + c = 2 ^ e)
    (hmono : Mono n d (d + 5)) :
    5 ≤ c ∧ tm (c - 1) = (e : F) ∧
      ∃ v m : ℕ, 2 ≤ v ∧ Even v ∧ Odd m ∧ c - 1 = 2 ^ v * m := by
  have he : 0 < e := by
    by_contra hn
    have hz : e = 0 := by omega
    rw [hz, pow_zero] at hB
    omega
  have hEven := reflection_index_even e d c he hodd (by omega) hB
  have hc5 : 5 ≤ c := by
    obtain ⟨j, D, _, hN, _, hclass⟩ := reflection_cube (c - 1) (by omega) hEven (1 + (e : F))
    have hb := bound_from_cube e d c n (d + 5) j D hd hodd hc hB hN hclass hmono
    omega
  have hnot : 1 + (e : F) ≠ tm (c - 1) := by
    intro hs
    have hclass : ∀ z ∈ cube (c - 1), tm (0 + z) + tm (c - 1 - (0 + z)) = 1 + (e : F) := by
      intro z hz
      simpa only [Nat.zero_add, hs] using cube_reflection (c - 1) z hz
    have hb := bound_from_cube e d c n (d + 5) 0 (c - 1) hd hodd hc hB (by omega) hclass hmono
    omega
  have hpar : tm (c - 1) = (e : F) := by
    have ho := f2_opposite (1 + (e : F)) (tm (c - 1)) hnot
    exact (add_left_cancel ho).symm
  obtain ⟨v, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : c - 1 ≠ 0)
  have hvpos : 0 < v := by
    by_contra hn
    have hvzero : v = 0 := by omega
    rw [hvzero, pow_zero, Nat.one_mul] at hNm
    have hzero : (m : F) = 0 := by simpa only [hNm] using hEven.natCast_zmod_two
    exact zero_ne_one (hzero.symm.trans hm.natCast_zmod_two)
  have hvnot : ¬ Odd v := by
    intro hvodd
    have hDdiv : 2 ^ 1 ∣ (c - 1) - 2 := Nat.dvd_sub hEven.two_dvd (dvd_refl 2)
    have hdiff : tm ((c - 1) - 2) + tm (c - 1) = 1 := by
      have h := tm_sub_power_difference v m 1 hm hvpos
      have hone : (1 : F) + 1 + 1 = 1 := by decide
      simpa only [← hNm, hvodd.natCast_zmod_two, Nat.cast_one, hone, pow_one] using h
    have hDpar : tm ((c - 1) - 2) = 1 + (e : F) := by
      have hh := CharTwo.add_eq_iff_eq_add.1 hdiff
      rwa [hpar] at hh
    have hclass : ∀ z ∈ cube ((c - 1) - 2), tm (1 + z) + tm (c - 1 - (1 + z)) = 1 + (e : F) := by
      intro z hz
      rw [← hDpar]
      exact shifted_cube_reflection 1 1 ((c - 1) - 2) (c - 1) z hDdiv (by decide) (by omega) hz
    have hb := bound_from_cube e d c n (d + 5) 1 ((c - 1) - 2) hd hodd hc hB (by omega) hclass hmono
    omega
  have hvEven : Even v := (Nat.even_or_odd v).resolve_right hvnot
  have hvge : 2 ≤ v := by obtain ⟨k, hk⟩ := hvEven; omega
  exact ⟨hc5, hpar, v, m, hvge, hvEven, hm, hNm⟩

#print axioms equality_parameters
end TmConfiguration
```

### `TmArc.lean`

```lean
import TmEquality
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

namespace TmArc

lemma small_interval_congruence_unique (m : ℕ) (hm : 0 < m) (a b : ℤ)
    (ha0 : -(m : ℤ) ≤ a) (ha1 : a ≤ m) (hb0 : -(m : ℤ) ≤ b) (hb1 : b ≤ m)
    (h : a ≡ b [ZMOD 4 * (m : ℤ)]) : a = b := by
  have h' := (h.add_right (m : ℤ)).eq
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ a + m) (by omega : a + m < 4 * (m : ℤ)),
    Int.emod_eq_of_lt (by omega : 0 ≤ b + m) (by omega : b + m < 4 * (m : ℤ))] at h'
  omega

/-- In an arc of span m on a circle of length 4m, a unit progression of m points
must use a step congruent to +1 or -1. -/
lemma short_arc_unit_progression (m : ℕ) (hm : 3 ≤ m) (u : ℤ) (x : ℕ → ℤ)
    (hlo : ∀ i < m, 0 ≤ x i) (hhi : ∀ i < m, x i ≤ m)
    (hstep : ∀ i, i + 1 < m → x (i + 1) - x i ≡ u [ZMOD 4 * (m : ℤ)])
    (hunit : ¬ u ≡ 0 [ZMOD 4 * (m : ℤ)]) :
    u ≡ 1 [ZMOD 4 * (m : ℤ)] ∨ u ≡ -1 [ZMOD 4 * (m : ℤ)] := by
  let h := x 1 - x 0
  have h0 := hstep 0 (by omega)
  have hconst : ∀ i, i + 1 < m → x (i + 1) - x i = h := by
    intro i hi
    apply small_interval_congruence_unique m (by omega)
    · have h1 := hlo (i + 1) hi
      have h2 := hhi i (by omega)
      omega
    · have h1 := hhi (i + 1) hi
      have h2 := hlo i (by omega)
      omega
    · have h1 := hlo 1 (by omega)
      have h2 := hhi 0 (by omega)
      dsimp [h]
      omega
    · have h1 := hhi 1 (by omega)
      have h2 := hlo 0 (by omega)
      dsimp [h]
      omega
    · exact (hstep i hi).trans h0.symm
  have hform : ∀ i, i < m → x i = x 0 + (i : ℤ) * h := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hnext := hconst i hi
      push_cast
      nlinarith only [hprev, hnext]
  have hlast := hform (m - 1) (by omega)
  have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  rw [hcast] at hlast
  have hleft0 := hlo 0 (by omega)
  have hleft1 := hhi 0 (by omega)
  have hright0 := hlo (m - 1) (by omega)
  have hright1 := hhi (m - 1) (by omega)
  have hlower : -1 ≤ h := by
    by_contra hn
    have hle : h ≤ -2 := by omega
    have hmz : (3 : ℤ) ≤ m := by omega
    nlinarith
  have hupper : h ≤ 1 := by
    by_contra hn
    have hle : 2 ≤ h := by omega
    have hmz : (3 : ℤ) ≤ m := by omega
    nlinarith
  have hne : h ≠ 0 := by
    intro hz
    apply hunit
    have hmod : h ≡ u [ZMOD 4 * (m : ℤ)] := h0
    rw [hz] at hmod
    exact hmod.symm
  have hs : h = 1 ∨ h = -1 := by omega
  have hmod : u ≡ h [ZMOD 4 * (m : ℤ)] := h0.symm
  rcases hs with hs | hs
  · exact Or.inl (by simpa only [hs] using hmod)
  · exact Or.inr (by simpa only [hs] using hmod)

#print axioms short_arc_unit_progression
end TmArc
```

### `TmBoundary.lean`

```lean
import TmConfiguration
import TmArc

namespace TmBoundary
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmOrbit TmAttainment

lemma three_point_obstruction (a : ℕ) :
    ¬ ((a + 6) % 64 ≤ 16 ∧ (a + 18) % 64 ≤ 16 ∧ (a + 54) % 64 ≤ 16) := by omega

lemma boundary_large (e n : ℕ) (hodd : Odd e) (hB : 128 ≤ 2 ^ e)
    (hrem : n % (2 ^ e) = 2 ^ e - 3)
    (hmono : Mono n (2 ^ e - 5) (2 ^ e)) : False := by
  let B := 2 ^ e
  let m := n / B
  have hn : n = B * m + (B - 3) := by
    have h := Nat.mod_add_div n B
    change n % B = B - 3 at hrem
    dsimp [m]
    omega
  have hecast : (e : F) = 1 := hodd.natCast_zmod_two
  have hr32 : tm (B - 33) = 0 := by
    have hi : B - 33 = B - 1 - 32 := by omega
    rw [hi, tm_dyadic_complement e 32 (by omega), hecast]
    have hsmall : tm 32 = 1 := by decide
    rw [hsmall]
    decide
  have hr37 : tm (B - 38) = 0 := by
    have hi : B - 38 = B - 1 - 37 := by omega
    rw [hi, tm_dyadic_complement e 37 (by omega), hecast]
    have hsmall : tm 37 = 1 := by decide
    rw [hsmall]
    decide
  have hr42 : tm (B - 43) = 0 := by
    have hi : B - 43 = B - 1 - 42 := by omega
    rw [hi, tm_dyadic_complement e 42 (by omega), hecast]
    have hsmall : tm 42 = 1 := by decide
    rw [hsmall]
    decide
  have hi6 : n + 6 * (B - 5) = B * (m + 6) + (B - 33) := by rw [Nat.mul_add]; omega
  have hi7 : n + 7 * (B - 5) = B * (m + 7) + (B - 38) := by rw [Nat.mul_add]; omega
  have hi8 : n + 8 * (B - 5) = B * (m + 8) + (B - 43) := by rw [Nat.mul_add]; omega
  have h6 := hmono 6 (by omega)
  have h7 := hmono 7 (by omega)
  have h8 := hmono 8 (by omega)
  change tm (n + 6 * (B - 5)) = tm n at h6
  change tm (n + 7 * (B - 5)) = tm n at h7
  change tm (n + 8 * (B - 5)) = tm n at h8
  rw [hi6, tm_dyadic_block e (m + 6) (B - 33) (by omega), hr32, add_zero] at h6
  rw [hi7, tm_dyadic_block e (m + 7) (B - 38) (by omega), hr37, add_zero] at h7
  rw [hi8, tm_dyadic_block e (m + 8) (B - 43) (by omega), hr42, add_zero] at h8
  apply tm_no_triple (m + 6)
  exact ⟨by simpa only [Nat.add_assoc] using h6.trans h7.symm,
    by simpa only [Nat.add_assoc] using h7.trans h8.symm⟩

lemma boundary_32 (n : ℕ) (hrem : n % 32 = 29) (hmono : Mono n 27 32) : False := by
  let m := n / 32
  have hn : n = 32 * m + 29 := by have h := Nat.mod_add_div n 32; omega
  have hi5 : n + 5 * 27 = 32 * (m + 5) + 4 := by omega
  have hi7 : n + 7 * 27 = 32 * (m + 6) + 26 := by omega
  have hi8 : n + 8 * 27 = 32 * (m + 7) + 21 := by omega
  have h5 := hmono 5 (by decide)
  have h7 := hmono 7 (by decide)
  have h8 := hmono 8 (by decide)
  have hpow : (2 : ℕ) ^ 5 = 32 := by decide
  have hblock (q r : ℕ) (hr : r < 32) : tm (32 * q + r) = tm q + tm r := by
    simpa only [hpow] using tm_dyadic_block 5 q r (by simpa only [hpow] using hr)
  have hword4 : tm 4 = 1 := by decide
  have hword26 : tm 26 = 1 := by decide
  have hword21 : tm 21 = 1 := by decide
  rw [hi5, hblock (m + 5) 4 (by decide), hword4] at h5
  rw [hi7, hblock (m + 6) 26 (by decide), hword26] at h7
  rw [hi8, hblock (m + 7) 21 (by decide), hword21] at h8
  apply tm_no_triple (m + 5)
  exact ⟨by simpa only [Nat.add_assoc] using add_right_cancel (h5.trans h7.symm),
    by simpa only [Nat.add_assoc] using add_right_cancel (h7.trans h8.symm)⟩

#print axioms boundary_large
#print axioms boundary_32
end TmBoundary
```

### `TmC5.lean`

```lean
import TmBoundary

namespace TmC5
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmOrbit TmAttainment
open TmArcBridge TmConfiguration TmBoundary

lemma singleton_arc_start (B d n u a : ℕ) (hB : d + 5 = B)
    (hdumod : d * u ≡ 1 [MOD B])
    (ha : (a : ZMod B) = -(u : ZMod B) * (n : ZMod B) + 1)
    (hpoint : (a + u * 2) % B = 0) : n % B = B - 3 := by
  have hdu : (d : ZMod B) * (u : ZMod B) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ B).2 hdumod
    simpa only [Nat.cast_mul, Nat.cast_one] using h
  have hpoint' : (a : ZMod B) + (u : ZMod B) * 2 = 0 := by
    have h := congrArg (fun x : ℕ => (x : ZMod B)) hpoint
    simpa only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero] using h
  have hh := congrArg (fun x : ZMod B => (d : ZMod B) * x) hpoint'
  have hid : (d : ZMod B) * ((a : ZMod B) + (u : ZMod B) * 2) =
      ((d : ZMod B) + 2) - (n : ZMod B) := by
    rw [ha]
    calc
      _ = -((d : ZMod B) * (u : ZMod B)) * (n : ZMod B) +
          (d : ZMod B) + ((d : ZMod B) * (u : ZMod B)) * 2 := by ring
      _ = _ := by rw [hdu]; ring
  rw [hid, mul_zero] at hh
  have hcast : (n : ZMod B) = ((d + 2 : ℕ) : ZMod B) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (sub_eq_zero.1 hh).symm
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ B).1 hcast
  have hidx : d + 2 = B - 3 := by omega
  have hsmall : B - 3 < B := by omega
  simpa only [Nat.ModEq, hidx, Nat.mod_eq_of_lt hsmall] using hmod

lemma c_five_no_attainment (e d n : ℕ) (hd : 0 < d) (hodd : Odd d)
    (hB : d + 5 = 2 ^ e) (hlarge : 16 ≤ 2 ^ e)
    (hmono : Mono n d (d + 5)) : False := by
  have hpars := equality_parameters e d 5 n hd hodd (by decide) hB hmono
  have hecast : (e : F) = 1 := hpars.2.1.symm.trans (by decide : tm (5 - 1) = 1)
  have heodd : Odd e := ZMod.natCast_eq_one_iff_odd.1 hecast
  have hMonoB : Mono n d (2 ^ e) := by simpa only [hB] using hmono
  have hclass : ∀ z ∈ cube 0, tm (2 + z) + tm (5 - 1 - (2 + z)) = 1 + (e : F) := by
    intro z hz
    have hz0 : z = 0 := Nat.eq_zero_of_le_zero (cube_mem_le 0 z hz)
    subst z
    rw [hecast]
    decide
  obtain ⟨u, a, _, _, _, hdumod, _, ha, harc⟩ :=
    forced_set_arc e d 5 n (2 ^ e) 2 0 hd hodd (by decide) hB (by decide)
      hclass (by omega) hMonoB
  have hpoint : (a + u * 2) % (2 ^ e) = 0 := by
    have hr := harc 2 (by decide) (by rw [hecast]; decide)
    omega
  have ha' : (a : ZMod (2 ^ e)) = -(u : ZMod (2 ^ e)) * (n : ZMod (2 ^ e)) + 1 := by
    simpa only [Nat.sub_self, Nat.zero_add, Nat.cast_one] using ha
  have hrem := singleton_arc_start (2 ^ e) d n u a hB hdumod ha' hpoint
  have he4 : 4 ≤ e := by
    by_contra hn
    have he3 : e ≤ 3 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he3
    have h8 : (2 : ℕ) ^ 3 = 8 := by decide
    rw [h8] at hp
    omega
  by_cases he5 : e = 5
  · subst e
    have h32 : (2 : ℕ) ^ 5 = 32 := by decide
    rw [h32] at hB hrem hMonoB
    have hd27 : d = 27 := by omega
    rw [hd27] at hMonoB
    exact boundary_32 n (by simpa using hrem) hMonoB
  · have he7 : 7 ≤ e := by obtain ⟨k, hk⟩ := heodd; omega
    have h128 : 128 ≤ 2 ^ e := by
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he7
      have hpow : (2 : ℕ) ^ 7 = 128 := by decide
      simpa only [hpow] using hp
    have hdidx : d = 2 ^ e - 5 := by omega
    exact boundary_large e n heodd h128 hrem (by simpa only [hdidx] using hMonoB)

#print axioms c_five_no_attainment
end TmC5
```

### `TmRigidityData.lean`

```lean
import TmC5
import TmEquality

namespace TmRigidityData
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmOrbit TmAttainment
open TmConfiguration TmArcBridge TmEquality

lemma inverse_sign (B M d u : ℕ) (hM : 1 < M) (hd : 1 ≤ d) (hdiv : M ∣ B)
    (hinv : d * u ≡ 1 [MOD B]) (hsign : u % M = 1 ∨ u % M + 1 = M) :
    M ∣ d - 1 ∨ M ∣ d + 1 := by
  have hinvM := hinv.of_dvd hdiv
  have hOne : 1 % M = 1 := Nat.mod_eq_of_lt hM
  rcases hsign with hp | hm
  · have humod : u ≡ 1 [MOD M] := by change u % M = 1 % M; rwa [hOne]
    have hdmod : d ≡ 1 [MOD M] := by
      have hh := (humod.mul_left d).symm.trans hinvM
      simpa only [Nat.mul_one] using hh
    exact Or.inl ((Nat.modEq_iff_dvd' hd).1 hdmod.symm)
  · have humod : u + 1 ≡ 0 [MOD M] := by
      change (u + 1) % M = 0 % M
      rw [Nat.add_mod, hOne, hm, Nat.mod_self, Nat.zero_mod]
    have hdu : M ∣ d * u + d := by
      have hh := dvd_mul_of_dvd_right (Nat.modEq_zero_iff_dvd.1 humod) d
      simpa only [Nat.mul_add, Nat.mul_one] using hh
    have hzero := Nat.modEq_zero_iff_dvd.2 hdu
    have hright := (hinvM.add_right d).symm.trans hzero
    exact Or.inr (by simpa only [Nat.add_comm] using Nat.modEq_zero_iff_dvd.1 hright)

structure EqualityData (e d c : ℕ) where
  u : ℕ
  a : ℕ
  v : ℕ
  s : ℕ
  E : ℕ
  u_bound : u < 2 ^ e
  u_odd : Odd u
  u_coprime : Nat.Coprime (2 ^ e) u
  inverse : d * u ≡ 1 [MOD 2 ^ e]
  exponent : e = v + s
  degree : c - 5 = 2 ^ v * E
  E_odd : Odd E
  E_pos : 1 ≤ E
  E_small : 2 * E < 2 ^ s
  sign : 2 ^ s ∣ d - 1 ∨ 2 ^ s ∣ d + 1
  arc : ∀ r < c, tm r + tm (c - 1 - r) = 1 + (e : F) →
    (a + u * r) % (2 ^ e) ≤ c - 5

lemma equality_data (e d c n : ℕ)
    (hd : 0 < d) (hodd : Odd d) (hc : 6 ≤ c) (hB : d + c = 2 ^ e)
    (hleast : 2 ^ e < 2 * d) (hmono : Mono n d (d + 5)) :
    Nonempty (EqualityData e d c) := by
  obtain ⟨hc5, hpar, vN, mN, hvN, hvEven, hmN, hNm⟩ :=
    equality_parameters e d c n hd hodd (by omega) hB hmono
  have hNdiv : 4 ∣ c - 1 := by
    rw [hNm]
    have hp : (2 : ℕ) ^ 2 ∣ 2 ^ vN := pow_dvd_pow 2 hvN
    exact dvd_mul_of_dvd_left hp mN
  have hDdiv : 2 ^ 2 ∣ c - 5 := by
    have hh := Nat.dvd_sub hNdiv (dvd_refl 4)
    have hp : (2 : ℕ) ^ 2 = 4 := by decide
    have hsum : (1 : ℕ) + 4 = 5 := by decide
    simpa only [Nat.sub_sub, hp, hsum] using hh
  have hDpar : tm (c - 5) = 1 + (e : F) := by
    have hh := tm_sub_power_difference vN mN 2 hmN hvN
    have hvcast : (vN : F) = 0 := hvEven.natCast_zmod_two
    have htwo : ((2 : ℕ) : F) = 0 := by decide
    have hpow : (2 : ℕ) ^ 2 = 4 := by decide
    have hdiff : tm (c - 5) + tm (c - 1) = 1 := by
      simpa only [← hNm, hvcast, htwo, hpow, add_zero, Nat.sub_sub] using hh
    have hh' := CharTwo.add_eq_iff_eq_add.1 hdiff
    rwa [hpar] at hh'
  have hclass : ∀ z ∈ cube (c - 5), tm (2 + z) + tm (c - 1 - (2 + z)) = 1 + (e : F) := by
    intro z hz
    rw [← hDpar]
    exact shifted_cube_reflection 2 2 (c - 5) (c - 1) z hDdiv (by decide) (by omega) hz
  obtain ⟨u, a, huB, huodd, hucop, hinv, _, _, harc⟩ :=
    forced_set_arc e d c n (d + 5) 2 (c - 5) hd hodd (by omega) hB (by omega)
      hclass (by omega) hmono
  have harc' : ∀ r < c, tm r + tm (c - 1 - r) = 1 + (e : F) →
      (a + u * r) % (2 ^ e) ≤ c - 5 := by
    have hspan : 2 ^ e - (d + 5) = c - 5 := by omega
    simpa only [hspan] using harc
  have hDpos : 0 < c - 5 := by omega
  obtain ⟨v, E, hEOdd, hDE⟩ := Nat.exists_eq_two_pow_mul_odd hDpos.ne'
  have hEpos : 1 ≤ E := by obtain ⟨k, hk⟩ := hEOdd; omega
  have hDsmall : c - 5 < 2 ^ e := by omega
  have h2D : 2 * (c - 5) < 2 ^ e := by omega
  have hvlt : v < e := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
    have hh : 2 ^ v ≤ c - 5 := by rw [hDE]; exact Nat.le_mul_of_pos_right _ hEpos
    omega
  let s := e - v
  have heq : e = v + s := by dsimp [s]; omega
  have hpowB : 2 ^ e = 2 ^ v * 2 ^ s := by rw [heq, pow_add]
  have hsmall : 2 * E < 2 ^ s := by
    by_contra hn
    have hh := Nat.mul_le_mul_left (2 ^ v) (show 2 ^ s ≤ 2 * E by omega)
    rw [hDE, hpowB] at h2D
    nlinarith only [hh, h2D]
  have harcCube : ∀ z ∈ cube (2 ^ v * E),
      ((a + u * 2) + u * z) % (2 ^ (v + s)) ≤ 2 ^ v * E := by
    intro z hz
    have hz' : z ∈ cube (c - 5) := by simpa only [hDE] using hz
    have hzle := cube_mem_le (c - 5) z hz'
    have hr := harc' (2 + z) (by omega) (hclass z hz')
    have hidx : a + u * (2 + z) = (a + u * 2) + u * z := by ring
    simpa only [hidx, heq, hDE] using hr
  have hcop' : Nat.Coprime (2 ^ (v + s)) u := by simpa only [← heq] using hucop
  have hsign := compressed_cube_rigidity v s E u (a + u * 2) hEpos hsmall hEOdd huodd hcop' harcCube
  have hMdiv : 2 ^ s ∣ 2 ^ e := pow_dvd_pow 2 (by dsimp [s]; omega)
  have hM : 1 < 2 ^ s := by omega
  have hdSign := inverse_sign (2 ^ e) (2 ^ s) d u hM (by omega) hMdiv hinv hsign
  exact ⟨⟨u, a, v, s, E, huB, huodd, hucop, hinv, heq, hDE, hEOdd, hEpos, hsmall, hdSign, harc'⟩⟩

#print axioms equality_data
end TmRigidityData
```

### `TmValArithmetic.lean`

```lean
import TmRigidityData

namespace TmValArithmetic
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmRigidityData

lemma odd_factor_power_divides (k v E : ℕ) (hE : Odd E) (hdiv : 2 ^ k ∣ 2 ^ v * E) : k ≤ v := by
  have hcop : Nat.Coprime (2 ^ k) E := hE.coprime_two_left.pow_left k
  have hp : 2 ^ k ∣ 2 ^ v := hcop.dvd_of_dvd_mul_right hdiv
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).1 hp

lemma odd_valuation_unique (a b c d : ℕ) (hb : Odd b) (hd : Odd d)
    (h : 2 ^ a * b = 2 ^ c * d) : a = c := by
  apply Nat.le_antisymm
  · apply odd_factor_power_divides a c d hd
    rw [← h]
    exact dvd_mul_right _ _
  · apply odd_factor_power_divides c a b hb
    rw [h]
    exact dvd_mul_right _ _

lemma high_reflection_valuation_impossible (e d c n vN mN : ℕ)
    (hd : 0 < d) (hodd : Odd d) (hc : 6 ≤ c) (hB : d + c = 2 ^ e)
    (hleast : 2 ^ e < 2 * d) (hmono : Mono n d (d + 5))
    (hvN : 4 ≤ vN) (hvEven : Even vN) (hmOdd : Odd mN)
    (hNm : c - 1 = 2 ^ vN * mN) (hpar : tm (c - 1) = (e : F)) : False := by
  obtain ⟨dat⟩ := equality_data e d c n hd hodd hc hB hleast hmono
  have hNdiv : 16 ∣ c - 1 := by
    rw [hNm]
    have hp : (2 : ℕ) ^ 4 ∣ 2 ^ vN := pow_dvd_pow 2 hvN
    exact dvd_mul_of_dvd_left hp mN
  obtain ⟨q, hq⟩ := hNdiv
  have hqpos : 1 ≤ q := by omega
  have hEOdd : Odd (4 * q - 1) := ⟨2 * q - 1, by omega⟩
  have hpow2 : (2 : ℕ) ^ 2 = 4 := by decide
  have hDE : 2 ^ dat.v * dat.E = 2 ^ 2 * (4 * q - 1) := by
    rw [← dat.degree, hpow2]
    omega
  have hv : dat.v = 2 := odd_valuation_unique dat.v dat.E 2 (4 * q - 1) dat.E_odd hEOdd hDE
  have hexp : e = 2 + dat.s := by simpa only [hv] using dat.exponent
  let M := 2 ^ dat.s
  have hMpos : 0 < M := pow_pos (by decide) _
  have hB4 : 2 ^ e = 4 * M := by rw [hexp, pow_add, hpow2]
  have hNlt : c - 1 < 2 * M := by omega
  have hs2 : 2 ≤ dat.s := by
    by_contra hn
    have hs1 : dat.s ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hs1
    simp only [pow_one] at hp
    change M ≤ 2 at hp
    omega
  have h4M : 4 ∣ M := by
    have hp : (2 : ℕ) ^ 2 ∣ 2 ^ dat.s := pow_dvd_pow 2 hs2
    simpa only [hpow2] using hp
  have h4B : 4 ∣ 2 ^ e := ⟨M, hB4⟩
  have h4N : 4 ∣ c - 1 := ⟨4 * q, by omega⟩
  have h4dplus : 4 ∣ d + 1 := by
    have hh := Nat.dvd_sub h4B h4N
    have hi : 2 ^ e - (c - 1) = d + 1 := by omega
    rwa [hi] at hh
  have hMplus : M ∣ d + 1 := by
    rcases dat.sign with hm | hm
    · have h4minus := h4M.trans hm
      have hh := Nat.dvd_sub h4dplus h4minus
      have hi : (d + 1) - (d - 1) = 2 := by omega
      rw [hi] at hh
      exact False.elim ((by decide : ¬ (4 : ℕ) ∣ 2) hh)
    · exact hm
  have hMB : M ∣ 2 ^ e := ⟨4, by rw [hB4]; ring⟩
  have hMN : M ∣ c - 1 := by
    have hh := Nat.dvd_sub hMB hMplus
    have hi : 2 ^ e - (d + 1) = c - 1 := by omega
    rwa [hi] at hh
  obtain ⟨k, hk⟩ := hMN
  have hkpos : 1 ≤ k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.mul_zero] at hk
    omega
  have hkone : k = 1 := by
    by_contra hn
    have hk2 : 2 ≤ k := by omega
    have hh := Nat.mul_le_mul_left M hk2
    omega
  have hNeq : c - 1 = M := by simpa only [hkone, Nat.mul_one] using hk
  have hfactor : 2 ^ vN * mN = 2 ^ dat.s * 1 := by rw [← hNm, hNeq, Nat.mul_one]
  have hvNs : vN = dat.s := odd_valuation_unique vN mN dat.s 1 hmOdd (by decide) hfactor
  have hsEven : Even dat.s := hvNs ▸ hvEven
  have heEven : Even e := by rw [hexp]; exact (by decide : Even (2 : ℕ)).add hsEven
  have hEzero : (e : F) = 0 := heEven.natCast_zmod_two
  have hNword : tm (c - 1) = 1 := by
    rw [hNeq]
    simpa only [Nat.mul_one, TmAttainment.tm_one] using tm_scale dat.s 1
  exact zero_ne_one (hEzero.symm.trans (hpar.symm.trans hNword))

#print axioms high_reflection_valuation_impossible
end TmValArithmetic
```

### `TmLowValuation.lean`

```lean
import TmValArithmetic

namespace TmLowValuation
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmRigidityData TmValArithmetic

lemma low_reflection_parameters (e d c m : ℕ) (dat : EqualityData e d c)
    (hd : 0 < d) (hc : 6 ≤ c) (hB : d + c = 2 ^ e)
    (hpar : tm (c - 1) = (e : F)) (hmOdd : Odd m) (hNm : c - 1 = 4 * m) :
    dat.s = 2 ∧ dat.E = 1 ∧ Even dat.v ∧ 4 ≤ dat.v := by
  have hD8 : 8 ∣ c - 5 := by
    obtain ⟨k, hk⟩ := hmOdd
    exact ⟨k, by omega⟩
  have hpow3 : (2 : ℕ) ^ 3 = 8 := by decide
  have hv3 : 3 ≤ dat.v := by
    apply odd_factor_power_divides 3 dat.v dat.E dat.E_odd
    rw [hpow3, ← dat.degree]
    exact hD8
  have hs2 : 2 ≤ dat.s := by
    by_contra hn
    have hs1 : dat.s ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hs1
    simp only [pow_one] at hp
    have hh := dat.E_small
    have hE := dat.E_pos
    omega
  let M := 2 ^ dat.s
  have hpow2 : (2 : ℕ) ^ 2 = 4 := by decide
  have h4M : 4 ∣ M := by
    have hp : (2 : ℕ) ^ 2 ∣ 2 ^ dat.s := pow_dvd_pow 2 hs2
    simpa only [hpow2] using hp
  have h4D : 4 ∣ c - 5 := (by decide : (4 : ℕ) ∣ 8).trans hD8
  have hMB : M ∣ 2 ^ e := pow_dvd_pow 2 (by have hh := dat.exponent; omega)
  have hMplus : M ∣ d + 1 := by
    rcases dat.sign with hm | hm
    · have hh := Nat.dvd_sub hMB hm
      have hi : 2 ^ e - (d - 1) = (c - 5) + 6 := by omega
      rw [hi] at hh
      have h4D6 := h4M.trans hh
      have h4six := Nat.dvd_sub h4D6 h4D
      have hsub : ((c - 5) + 6) - (c - 5) = 6 := by omega
      rw [hsub] at h4six
      exact False.elim ((by decide : ¬ (4 : ℕ) ∣ 6) h4six)
    · exact hm
  have hMD4 : M ∣ (c - 5) + 4 := by
    have hh := Nat.dvd_sub hMB hMplus
    have hi : 2 ^ e - (d + 1) = (c - 5) + 4 := by omega
    rwa [hi] at hh
  have hsEq : dat.s = 2 := by
    by_contra hn
    have hs3 : 3 ≤ dat.s := by omega
    have h8M : 8 ∣ M := by
      have hp : (2 : ℕ) ^ 3 ∣ 2 ^ dat.s := pow_dvd_pow 2 hs3
      simpa only [hpow3] using hp
    have hh := Nat.dvd_sub (h8M.trans hMD4) hD8
    have hi : ((c - 5) + 4) - (c - 5) = 4 := by omega
    rw [hi] at hh
    exact (by decide : ¬ (8 : ℕ) ∣ 4) hh
  have hEEq : dat.E = 1 := by
    have hh := dat.E_small
    rw [hsEq, hpow2] at hh
    have hp := dat.E_pos
    omega
  have hDE : c - 5 = 2 ^ dat.v := by simpa only [hEEq, Nat.mul_one] using dat.degree
  have heq : e = dat.v + 2 := by simpa only [hsEq] using dat.exponent
  have hD8le : 8 ≤ 2 ^ dat.v := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hv3
    simpa only [hpow3] using hp
  have hNidx : c - 1 = 2 ^ dat.v * 1 + 4 := by omega
  have hNword : tm (c - 1) = 0 := by
    rw [hNidx, tm_dyadic_block dat.v 1 4 (by omega), TmAttainment.tm_one, TmAttainment.tm_four]
    decide
  have hEcast : (e : F) = 0 := hpar.symm.trans hNword
  have hvcast : (dat.v : F) = 0 := by
    have htwo : ((2 : ℕ) : F) = 0 := by decide
    simpa only [heq, Nat.cast_add, htwo, add_zero] using hEcast
  have hvEven : Even dat.v := ZMod.natCast_eq_zero_iff_even.1 hvcast
  have hv4 : 4 ≤ dat.v := by obtain ⟨k, hk⟩ := hvEven; omega
  exact ⟨hsEq, hEEq, hvEven, hv4⟩

#print axioms low_reflection_parameters
end TmLowValuation
```

### `TmArcNat.lean`

```lean
import TmArc

namespace TmArcNat
open TmArc

lemma residues_short_arc (m u a : ℕ) (hm : 3 ≤ m) (hcop : Nat.Coprime (4 * m) u)
    (harc : ∀ i < m, (a + u * i) % (4 * m) ≤ m) :
    u % (4 * m) = 1 ∨ u % (4 * m) + 1 = 4 * m := by
  let x : ℕ → ℤ := fun i => ((a + u * i) % (4 * m) : ℕ)
  have hlo : ∀ i < m, 0 ≤ x i := by
    intro i _
    change 0 ≤ (((a + u * i) % (4 * m) : ℕ) : ℤ)
    exact Int.natCast_nonneg _
  have hhi : ∀ i < m, x i ≤ m := by
    intro i hi
    change (((a + u * i) % (4 * m) : ℕ) : ℤ) ≤ (m : ℤ)
    exact_mod_cast harc i hi
  have hstep : ∀ i, i + 1 < m → x (i + 1) - x i ≡ (u : ℤ) [ZMOD 4 * (m : ℤ)] := by
    intro i _
    have h1 : x (i + 1) ≡ (a : ℤ) + (u : ℤ) * ((i + 1 : ℕ) : ℤ) [ZMOD 4 * (m : ℤ)] := by
      dsimp [x]
      exact_mod_cast Nat.mod_modEq (a + u * (i + 1)) (4 * m)
    have h0 : x i ≡ (a : ℤ) + (u : ℤ) * (i : ℤ) [ZMOD 4 * (m : ℤ)] := by
      dsimp [x]
      exact_mod_cast Nat.mod_modEq (a + u * i) (4 * m)
    have hh := h1.sub h0
    have hi : ((a : ℤ) + (u : ℤ) * ((i + 1 : ℕ) : ℤ)) -
        ((a : ℤ) + (u : ℤ) * (i : ℤ)) = (u : ℤ) := by push_cast; ring
    rwa [hi] at hh
  have hunit : ¬ (u : ℤ) ≡ 0 [ZMOD 4 * (m : ℤ)] := by
    intro hz
    have hnat : u ≡ 0 [MOD 4 * m] := by exact_mod_cast hz
    have hdiv := Nat.modEq_zero_iff_dvd.1 hnat
    have hself : Nat.Coprime (4 * m) (4 * m) := Nat.Coprime.of_dvd_right hdiv hcop
    simp only [Nat.coprime_self] at hself
    omega
  have hsign := short_arc_unit_progression m hm (u : ℤ) x hlo hhi hstep hunit
  have hM : 1 < 4 * m := by omega
  rcases hsign with hp | hn
  · have hnat : u ≡ 1 [MOD 4 * m] := by exact_mod_cast hp
    exact Or.inl (by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hM] using hnat)
  · have hplus : (u : ℤ) + 1 ≡ 0 [ZMOD 4 * (m : ℤ)] := by
      simpa using hn.add_right 1
    have hnat : u + 1 ≡ 0 [MOD 4 * m] := by exact_mod_cast hplus
    have hmod : (u % (4 * m) + 1) % (4 * m) = 0 := by
      have hz : (u + 1) % (4 * m) = 0 := by simpa only [Nat.ModEq, Nat.zero_mod] using hnat
      rw [Nat.add_mod, Nat.mod_eq_of_lt hM] at hz
      exact hz
    have hdiv := Nat.dvd_of_mod_eq_zero hmod
    have hh := Nat.le_of_dvd (by omega : 0 < u % (4 * m) + 1) hdiv
    have hlt := Nat.mod_lt u (by omega : 0 < 4 * m)
    exact Or.inr (by omega)

lemma divide_eight_arc (M m u a : ℕ)
    (harc : ∀ i < m, (a + u * (8 * i + 6)) % (8 * M) ≤ 8 * m) :
    ∀ i < m, ((a + 6 * u) / 8 + u * i) % M ≤ m := by
  intro i hi
  have hh : ((a + u * (8 * i + 6)) % (8 * M)) / 8 ≤ (8 * m) / 8 :=
    Nat.div_le_div_right (harc i hi)
  have hid : ((a + u * (8 * i + 6)) % (8 * M)) / 8 =
      ((a + 6 * u) / 8 + u * i) % M := by
    have heq : a + u * (8 * i + 6) = (a + 6 * u) + 8 * (u * i) := by ring
    rw [heq, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ (by decide)]
  have hright : (8 * m) / 8 = m := by omega
  rwa [hid, hright] at hh

#print axioms residues_short_arc
#print axioms divide_eight_arc
end TmArcNat
```

### `TmFamily.lean`

```lean
import TmLowValuation
import TmArcNat

namespace TmFamily
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmRigidityData
open TmValArithmetic TmLowValuation TmBoundary TmArcNat

lemma exceptional_family_impossible (e d c : ℕ) (dat : EqualityData e d c)
    (_hd : 0 < d) (hc : 6 ≤ c) (hB : d + c = 2 ^ e)
    (hs : dat.s = 2) (hE : dat.E = 1) (hvEven : Even dat.v) (hvge : 4 ≤ dat.v) : False := by
  let v := dat.v
  let D := 2 ^ v
  have hDE : c - 5 = D := by simpa only [hE, Nat.mul_one] using dat.degree
  have hcD : c = D + 5 := by omega
  have heq : e = v + 2 := by simpa only [hs] using dat.exponent
  have hpow2 : (2 : ℕ) ^ 2 = 4 := by decide
  have hpow3 : (2 : ℕ) ^ 3 = 8 := by decide
  have hB4 : 2 ^ e = 4 * D := by rw [heq, pow_add, hpow2]; ring
  have hdD : d + 5 = 3 * D := by omega
  have heEven : Even e := by rw [heq]; exact hvEven.add (by decide : Even (2 : ℕ))
  have hecast : (e : F) = 0 := heEven.natCast_zmod_two
  by_cases hv4 : v = 4
  · have hD16 : D = 16 := by dsimp [D]; rw [hv4]; decide
    have he6 : e = 6 := by omega
    have hB64 : 2 ^ e = 64 := by omega
    have hc21 : c = 21 := by omega
    have hd43 : d = 43 := by omega
    have hinv : 43 * dat.u ≡ 1 [MOD 64] := by simpa only [hd43, hB64] using dat.inverse
    have hother : 43 * 3 ≡ 1 [MOD 64] := by decide
    have humod : dat.u ≡ 3 [MOD 64] :=
      Nat.ModEq.cancel_left_of_coprime (by decide : Nat.gcd 64 43 = 1) (hinv.trans hother.symm)
    have huB : dat.u < 64 := by simpa only [hB64] using dat.u_bound
    have hu3 : dat.u = 3 := by
      change dat.u % 64 = 3 % 64 at humod
      rw [Nat.mod_eq_of_lt huB] at humod
      exact humod
    have h2 := dat.arc 2 (by omega) (by rw [hc21, he6]; decide)
    have h6 := dat.arc 6 (by omega) (by rw [hc21, he6]; decide)
    have h18 := dat.arc 18 (by omega) (by rw [hc21, he6]; decide)
    norm_num [hc21, hB64, hu3] at h2 h6 h18
    exact three_point_obstruction dat.a ⟨h2, h6, h18⟩
  · have hv6 : 6 ≤ v := by obtain ⟨k, hk⟩ := hvEven; change v = k + k at hk; omega
    let t := v - 3
    let m := 2 ^ t
    have ht3 : 3 ≤ t := by dsimp [t]; omega
    have hm8 : 8 ≤ m := by
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) ht3
      simpa only [hpow3] using hp
    have htOdd : Odd t := Nat.Even.sub_odd (by omega) hvEven (by decide)
    have htcast : (t : F) = 1 := htOdd.natCast_zmod_two
    have hvSplit : v = 3 + t := by dsimp [t]; omega
    have hD8 : D = 8 * m := by dsimp [D]; rw [hvSplit, pow_add, hpow3]
    have hB32 : 2 ^ e = 8 * (4 * m) := by rw [hB4, hD8]; ring
    have hc8 : c = 8 * m + 5 := by omega
    have hword6 : tm 6 = 0 := by decide
    have hblock (i : ℕ) : tm (8 * i + 6) = tm i := by
      have hh := tm_dyadic_block 3 i 6 (by decide)
      simpa only [hpow3, hword6, add_zero] using hh
    have hclasses : ∀ i < m, tm (8 * i + 6) + tm (c - 1 - (8 * i + 6)) = 1 + (e : F) := by
      intro i hi
      have hidx : c - 1 - (8 * i + 6) = 8 * (m - 1 - i) + 6 := by omega
      have hreflect : tm (m - 1 - i) = 1 + tm i := by
        have hh := tm_dyadic_complement t i hi
        simpa only [htcast] using hh
      rw [hidx, hblock, hblock, hreflect, hecast, add_zero]
      calc
        _ = (tm i + tm i) + 1 := by ring
        _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
    have harc8 : ∀ i < m, (dat.a + dat.u * (8 * i + 6)) % (8 * (4 * m)) ≤ 8 * m := by
      intro i hi
      have hh := dat.arc (8 * i + 6) (by omega) (hclasses i hi)
      simpa only [hB32, hDE, hD8] using hh
    have hMdiv : 4 * m ∣ 2 ^ e := ⟨8, by rw [hB32]; ring⟩
    have hcop : Nat.Coprime (4 * m) dat.u := Nat.Coprime.of_dvd_left hMdiv dat.u_coprime
    have hsmall := divide_eight_arc (4 * m) m dat.u dat.a harc8
    have hsign := residues_short_arc m dat.u ((dat.a + 6 * dat.u) / 8) (by omega) hcop hsmall
    have hdsign := inverse_sign (2 ^ e) (4 * m) d dat.u (by omega) (by omega) hMdiv dat.inverse hsign
    have hmul : 4 * m ∣ 24 * m := ⟨6, by ring⟩
    have hdShape : d + 5 = 24 * m := by omega
    rcases hdsign with hh | hh
    · have hdiv := Nat.dvd_sub hmul hh
      have hidx : 24 * m - (d - 1) = 6 := by omega
      rw [hidx] at hdiv
      have hbound := Nat.le_of_dvd (by decide : 0 < 6) hdiv
      omega
    · have hdiv := Nat.dvd_sub hmul hh
      have hidx : 24 * m - (d + 1) = 4 := by omega
      rw [hidx] at hdiv
      have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdiv
      omega

#print axioms exceptional_family_impossible
end TmFamily
```

### `TmFinal.lean`

```lean
import TmFamily

namespace TmFinal
open TmCore TmBinary TmCube TmReflection TmValuation TmFrobenius TmOrbit TmAttainment
open TmKnownCases TmConfiguration TmC5 TmRigidityData TmValArithmetic TmLowValuation TmFamily

/-- The full equality classification in Sobolewski's Conjecture 3. -/
theorem thueMorse_progression_bound_attained_iff (d : ℕ) (hd : 0 < d) :
    (∃ n : ℕ, Mono n d (d + 5)) ↔
      ∃ e : ℕ, 2 ≤ e ∧ Even e ∧ d + 1 = 2 ^ e := by
  constructor
  · rintro ⟨n, hmono⟩
    have hodd : Odd d := by
      rcases Nat.even_or_odd d with heven | hodd
      · exact False.elim (even_no_attainment d n hd heven hmono)
      · exact hodd
    have hdne : d ≠ 1 := by
      intro hd1
      subst d
      exact one_no_attainment n hmono
    have hd3 : 3 ≤ d := by obtain ⟨k, hk⟩ := hodd; omega
    have hex : ∃ e : ℕ, d < 2 ^ e := ⟨d, d.lt_two_pow_self⟩
    let e := Nat.find hex
    have hdb : d < 2 ^ e := Nat.find_spec hex
    have he2 : 2 ≤ e := by
      by_contra hn
      have he1 : e ≤ 1 := by omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he1
      simp only [pow_one] at hp
      omega
    have hepos : 0 < e := by omega
    have hprev : 2 ^ (e - 1) ≤ d := by
      have hmin := Nat.find_min hex (show e - 1 < e by omega)
      exact Nat.not_lt.1 hmin
    have htwoPrev : 2 ∣ 2 ^ (e - 1) := by
      have hp : (2 : ℕ) ^ 1 ∣ 2 ^ (e - 1) := pow_dvd_pow 2 (by omega)
      simpa only [pow_one] using hp
    have hprevlt : 2 ^ (e - 1) < d := by
      by_contra hn
      have heq : d = 2 ^ (e - 1) := by omega
      exact hodd.not_two_dvd_nat (heq ▸ htwoPrev)
    have hpow : 2 ^ e = 2 * 2 ^ (e - 1) := by
      have hi : e = (e - 1) + 1 := by omega
      calc
        _ = 2 ^ ((e - 1) + 1) := congrArg (fun x : ℕ => 2 ^ x) hi
        _ = _ := by rw [pow_succ, Nat.mul_comm]
    have hleast : 2 ^ e < 2 * d := by omega
    let c := 2 ^ e - d
    have hcpos : 1 ≤ c := by dsimp [c]; omega
    have hB : d + c = 2 ^ e := by dsimp [c]; omega
    by_cases hc1 : c = 1
    · have hdplus : d + 1 = 2 ^ e := by omega
      have hdiff : d = 2 ^ e - 1 := by omega
      have hlen : d + 5 = 2 ^ e + 4 := by omega
      have hm : Mono n (2 ^ e - 1) (2 ^ e + 4) := by
        have hh := hmono
        rw [hlen, hdiff] at hh
        exact hh
      obtain ⟨heven, hege⟩ := (mersenne_attainment_iff e hepos).1 ⟨n, hm⟩
      exact ⟨e, hege, heven, hdplus⟩
    · exfalso
      have hc3 : 3 ≤ c := by
        have heven := reflection_index_even e d c hepos hodd hcpos hB
        obtain ⟨k, hk⟩ := heven
        omega
      obtain ⟨hc5, hpar, vN, mN, hvN, hvEven, hmOdd, hNm⟩ :=
        equality_parameters e d c n hd hodd hc3 hB hmono
      by_cases hcEq : c = 5
      · have hB16 : 16 ≤ 2 ^ e := by
          have he4 : 4 ≤ e := by
            by_contra hn
            have he3 : e ≤ 3 := by omega
            have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he3
            have h8 : (2 : ℕ) ^ 3 = 8 := by decide
            rw [h8] at hp
            omega
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he4
          have h16 : (2 : ℕ) ^ 4 = 16 := by decide
          simpa only [h16] using hp
        exact c_five_no_attainment e d n hd hodd (by omega) hB16 hmono
      · have hc6 : 6 ≤ c := by omega
        by_cases hv2 : vN = 2
        · obtain ⟨dat⟩ := equality_data e d c n hd hodd hc6 hB hleast hmono
          have hpow2 : (2 : ℕ) ^ 2 = 4 := by decide
          have hNm4 : c - 1 = 4 * mN := by simpa only [hv2, hpow2] using hNm
          obtain ⟨hs, hE, hvEven', hvge⟩ := low_reflection_parameters e d c mN dat hd hc6 hB hpar hmOdd hNm4
          exact exceptional_family_impossible e d c dat hd hc6 hB hs hE hvEven' hvge
        · have hv4 : 4 ≤ vN := by obtain ⟨k, hk⟩ := hvEven; omega
          exact high_reflection_valuation_impossible e d c n vN mN hd hodd hc6 hB hleast
            hmono hv4 hvEven hmOdd hNm hpar
  · rintro ⟨e, he2, heven, hde⟩
    obtain ⟨n, hn⟩ := mersenne_attainment e he2 heven
    refine ⟨n, ?_⟩
    have hdiff : d = 2 ^ e - 1 := by omega
    have hlen : d + 5 = 2 ^ e + 4 := by omega
    rw [hlen, hdiff]
    exact hn

#print axioms TmOrbit.thueMorse_progression_bound
#print axioms thueMorse_progression_bound_attained_iff
end TmFinal
```

### `TmMaximum.lean`

```lean
import TmFinal
import Mathlib.Data.Nat.Find

namespace Campaign354240
open TmBinary

/-- The greatest attainable progression length up to the already-proved bound.
`A_is_maximum` proves that this is the greatest length among *all* progressions. -/
noncomputable def A (d : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun L : ℕ => ∃ n : ℕ, Mono n d L) (d + 5)

lemma A_le (d : ℕ) : A d ≤ d + 5 := by
  classical
  unfold A
  exact Nat.findGreatest_le _

lemma A_attained (d : ℕ) : ∃ n : ℕ, Mono n d (A d) := by
  classical
  unfold A
  apply Nat.findGreatest_spec (P := fun L : ℕ => ∃ n : ℕ, Mono n d L)
    (m := 0) (n := d + 5) (by omega)
  exact ⟨0, fun i hi => by omega⟩

lemma A_is_maximum (d : ℕ) (hd : 0 < d) :
    (∃ n : ℕ, Mono n d (A d)) ∧
      ∀ n L : ℕ, Mono n d L → L ≤ A d := by
  refine ⟨A_attained d, ?_⟩
  intro n L hmono
  classical
  unfold A
  exact Nat.le_findGreatest (TmOrbit.thueMorse_progression_bound d n L hd hmono) ⟨n, hmono⟩

/-- Sobolewski, arXiv:2204.05287, Conjecture 3, including its entire equality clause. -/
theorem sobolewski_conjecture_three (d : ℕ) (hd : 0 < d) :
    A d ≤ d + 5 ∧
      (A d = d + 5 ↔ ∃ e : ℕ, 2 ≤ e ∧ Even e ∧ d + 1 = 2 ^ e) := by
  refine ⟨A_le d, ?_⟩
  constructor
  · intro hA
    obtain ⟨n, hn⟩ := A_attained d
    rw [hA] at hn
    exact (TmFinal.thueMorse_progression_bound_attained_iff d hd).1 ⟨n, hn⟩
  · intro hfamily
    obtain ⟨n, hn⟩ := (TmFinal.thueMorse_progression_bound_attained_iff d hd).2 hfamily
    exact Nat.le_antisymm (A_le d) ((A_is_maximum d hd).2 n (d + 5) hn)

#print axioms A_is_maximum
#print axioms sobolewski_conjecture_three
end Campaign354240
```

### `TmUncapped.lean`

```lean
import TmMaximum
import Mathlib.Data.ENat.Lattice

namespace Campaign354240Literal
open TmBinary

/-- Source definition: first differing index; the empty infimum is infinity.
The matching indices are 0,...,l-1, so l is the number of matching terms. -/
noncomputable def Atn (n d : ℕ) : ℕ∞ :=
  ⨅ (l : ℕ) (_ : 1 ≤ l ∧ tm (n + l * d) ≠ tm n), (l : ℕ∞)

/-- Source definition, with no finite cutoff and no finiteness assumption. -/
noncomputable def At (d : ℕ) : ℕ∞ := ⨆ n : ℕ, Atn n d

lemma natCast_le_Atn_iff (n d L : ℕ) : (L : ℕ∞) ≤ Atn n d ↔ Mono n d L := by
  constructor
  · intro h i hi
    by_contra hne
    have hip : 1 ≤ i := by
      by_contra hn
      have : i = 0 := by omega
      subst i
      simp at hne
    have hli : (L : ℕ∞) ≤ (i : ℕ∞) :=
      h.trans (iInf_le_of_le i (iInf_le _ ⟨hip, hne⟩))
    have : L ≤ i := ENat.natCast_le_natCast.1 hli
    omega
  · intro h
    apply le_iInf
    intro l
    apply le_iInf
    intro hl
    apply ENat.natCast_le_natCast.2
    by_contra hlt
    exact hl.2 (h l (by omega))

lemma At_le_of_bound (d M : ℕ) (h : ∀ n L, Mono n d L → L ≤ M) :
    At d ≤ (M : ℕ∞) := by
  apply iSup_le
  intro n
  apply ENat.forall_natCast_le_iff_le.1
  intro L hL
  exact ENat.natCast_le_natCast.2 (h n L ((natCast_le_Atn_iff n d L).1 hL))

lemma length_le_At (n d L : ℕ) (h : Mono n d L) : (L : ℕ∞) ≤ At d :=
  ((natCast_le_Atn_iff n d L).2 h).trans (le_iSup (Atn · d) n)

/-- The former capped maximum equals the independently defined source supremum.
The universal maximum theorem, not just the definition of the cap, is used here. -/
lemma At_eq_maximum (d : ℕ) (hd : 0 < d) : At d = (Campaign354240.A d : ℕ∞) := by
  obtain ⟨⟨n, hn⟩, hmax⟩ := Campaign354240.A_is_maximum d hd
  exact le_antisymm (At_le_of_bound d _ hmax) (length_le_At n d _ hn)

lemma family_iff (d : ℕ) :
    (∃ e : ℕ, 2 ≤ e ∧ Even e ∧ d + 1 = 2 ^ e) ↔
      ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ d = 2 ^ k - 1 := by
  constructor
  · rintro ⟨k, hk, he, hd⟩
    exact ⟨k, hk, he, by omega⟩
  · rintro ⟨k, hk, he, hd⟩
    have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
    exact ⟨k, hk, he, by omega⟩

/-- Sobolewski, arXiv:2204.05287v2, Conjecture 3, for the uncapped source quantity. -/
theorem sobolewski_conjecture_three (d : ℕ) (hd : 1 ≤ d) :
    At d ≤ ((d + 5 : ℕ) : ℕ∞) ∧
      (At d = ((d + 5 : ℕ) : ℕ∞) ↔
        ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ d = 2 ^ k - 1) := by
  refine ⟨At_le_of_bound d (d + 5) (fun n L hm =>
    TmOrbit.thueMorse_progression_bound d n L hd hm), ?_⟩
  rw [At_eq_maximum d hd, ENat.natCast_inj]
  exact (Campaign354240.sobolewski_conjecture_three d hd).2.trans (family_iff d)

/-- The same conjecture bundled as a bound on every progression and sharp attainment. -/
theorem sobolewski_conjecture_three_bundled (d : ℕ) (hd : 1 ≤ d) :
    (∀ n L : ℕ, Mono n d L → L ≤ d + 5) ∧
      ((∃ n : ℕ, Mono n d (d + 5)) ↔
        ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ d = 2 ^ k - 1) := by
  exact ⟨fun n L hm => TmOrbit.thueMorse_progression_bound d n L hd hm,
    (TmFinal.thueMorse_progression_bound_attained_iff d hd).trans (family_iff d)⟩

lemma mono_one_le_two (n L : ℕ) (h : Mono n 1 L) : L ≤ 2 := by
  by_contra hlt
  apply tm_no_triple n
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [Nat.mul_one] at h1 h2
  exact ⟨h1.symm, h1.trans h2.symm⟩

/-- First three entries of the source's longest_progressions.csv, column "1". -/
theorem At_one : At 1 = 2 := by
  apply le_antisymm
  · exact At_le_of_bound 1 2 mono_one_le_two
  · exact length_le_At 1 1 2 (by
      intro i hi
      have h : i = 0 ∨ i = 1 := by omega
      rcases h with rfl | rfl <;> decide)

theorem At_two : At 2 = 2 := by
  apply le_antisymm
  · apply At_le_of_bound 2 2
    intro n L h
    exact mono_one_le_two (n / 2) L ((mono_double_iff n 1 L).1 h)
  · exact length_le_At 2 2 2 (by
      intro i hi
      have h : i = 0 ∨ i = 1 := by omega
      rcases h with rfl | rfl <;> decide)

theorem At_three : At 3 = 8 := by
  have h := (sobolewski_conjecture_three 3 (by decide)).2.mpr
    ⟨2, by decide, by decide, by decide⟩
  exact h

#check sobolewski_conjecture_three
#check sobolewski_conjecture_three_bundled
#eval Lean.versionString
#print axioms sobolewski_conjecture_three
#print axioms sobolewski_conjecture_three_bundled
#print axioms natCast_le_Atn_iff
#print axioms At_one
#print axioms At_two
#print axioms At_three
end Campaign354240Literal
```

