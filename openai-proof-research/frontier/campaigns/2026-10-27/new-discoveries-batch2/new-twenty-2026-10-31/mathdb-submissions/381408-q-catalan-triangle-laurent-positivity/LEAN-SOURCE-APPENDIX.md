# Lean source appendix

Modules are listed in import order.

## QGaussian.lean

```lean
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

open Polynomial
open scoped BigOperators

noncomputable section

namespace Catalan

/-- The polynomial [n] = 1 + X + ⋯ + X^(n-1). -/
def qInt (n : ℕ) : ℤ[X] := ∑ i ∈ Finset.range n, X ^ i

@[simp] theorem qInt_zero : qInt 0 = 0 := by simp [qInt]
@[simp] theorem qInt_one : qInt 1 = 1 := by simp [qInt]

theorem qInt_add (u v : ℕ) : qInt (u + v) = qInt u + X ^ u * qInt v := by
  unfold qInt
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp_rw [pow_add]

theorem qInt_mul_one_sub (n : ℕ) : qInt n * (1 - X) = 1 - X ^ n := by
  exact geom_sum_mul_neg _ _

theorem qInt_monic {n : ℕ} (hn : n ≠ 0) : (qInt n).Monic :=
  monic_geom_sum_X hn

theorem qInt_nonneg (n i : ℕ) : 0 ≤ (qInt n).coeff i := by
  rw [qInt, finsetSum_coeff]
  exact Finset.sum_nonneg fun j _ => by simp [coeff_X_pow, apply_ite]

/-- Gaussian Pascal recursion indexed by column and complementary column. -/
def rect : ℕ → ℕ → ℤ[X]
  | 0, _ => 1
  | _ + 1, 0 => 1
  | k + 1, l + 1 => rect (k + 1) l + X ^ (l + 1) * rect k (l + 1)

@[simp] theorem rect_zero_left (l : ℕ) : rect 0 l = 1 := by cases l <;> simp [rect]
@[simp] theorem rect_zero_right (k : ℕ) : rect k 0 = 1 := by cases k <;> simp [rect]

theorem rect_succ_succ (k l : ℕ) :
    rect (k + 1) (l + 1) = rect (k + 1) l + X ^ (l + 1) * rect k (l + 1) := by
  rw [rect]

/-- The Gaussian binomial with integer lower index, extended by zero. -/
def gauss (n : ℕ) (k : ℤ) : ℤ[X] :=
  if 0 ≤ k ∧ k ≤ n then rect k.toNat (n - k.toNat) else 0

theorem gauss_nat {n k : ℕ} (h : k ≤ n) : gauss n k = rect k (n - k) := by
  simp [gauss, h]

theorem gauss_rect (k l : ℕ) : gauss (k + l) k = rect k l := by
  rw [gauss_nat (Nat.le_add_right k l), Nat.add_sub_cancel_left]

theorem gauss_outside {n : ℕ} {k : ℤ} (h : k < 0 ∨ (n : ℤ) < k) : gauss n k = 0 := by
  unfold gauss
  rw [ite_eq_right]
  omega

/-- Product of the q-integers from 1 through n. -/
def qFactorial (n : ℕ) : ℤ[X] := ∏ i ∈ Finset.range n, qInt (i + 1)

@[simp] theorem qFactorial_zero : qFactorial 0 = 1 := by simp [qFactorial]

theorem qFactorial_succ (n : ℕ) :
    qFactorial (n + 1) = qFactorial n * qInt (n + 1) := by
  simp [qFactorial, Finset.prod_range_succ]

theorem qFactorial_monic (n : ℕ) : (qFactorial n).Monic := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ]
    exact ih.mul (qInt_monic (by omega))

theorem rect_factorial (k l : ℕ) :
    rect k l * (qFactorial k * qFactorial l) = qFactorial (k + l) := by
  induction k generalizing l with
  | zero => simp
  | succ k hk =>
    induction l with
    | zero => simp
    | succ l hl =>
      calc
        rect (k + 1) (l + 1) * (qFactorial (k + 1) * qFactorial (l + 1)) =
            (rect (k + 1) l * (qFactorial (k + 1) * qFactorial l)) * qInt (l + 1) +
            X ^ (l + 1) * (rect k (l + 1) * (qFactorial k * qFactorial (l + 1))) *
              qInt (k + 1) := by
          rw [rect_succ_succ]
          simp only [qFactorial_succ]
          ring
        _ = qFactorial (k + 1 + l) * (qInt (l + 1) + X ^ (l + 1) * qInt (k + 1)) := by
          rw [hl, hk, show k + (l + 1) = k + 1 + l by omega]
          ring
        _ = qFactorial (k + 1 + (l + 1)) := by
          rw [← qInt_add, show l + 1 + (k + 1) = k + 1 + l + 1 by omega]
          rw [show k + 1 + (l + 1) = (k + 1 + l) + 1 by omega, qFactorial_succ]

theorem gauss_factorial {n k : ℕ} (h : k ≤ n) :
    gauss n k * (qFactorial k * qFactorial (n - k)) = qFactorial n := by
  rw [gauss_nat h, rect_factorial, Nat.add_sub_of_le h]

theorem rect_monic (k l : ℕ) : (rect k l).Monic := by
  apply ((qFactorial_monic k).mul (qFactorial_monic l)).of_mul_monic_right
  rw [rect_factorial]
  exact qFactorial_monic _

theorem gauss_monic {n k : ℕ} (h : k ≤ n) : (gauss n k).Monic := by
  rw [gauss_nat h]
  exact rect_monic .. 

theorem rect_nonneg (k l i : ℕ) : 0 ≤ (rect k l).coeff i := by
  induction k generalizing l i with
  | zero => simp [coeff_one, apply_ite]
  | succ k hk =>
    induction l with
    | zero => simp [coeff_one, apply_ite]
    | succ l hl =>
      rw [rect_succ_succ, coeff_add, mul_comm (X ^ _), coeff_mul_X_pow']
      apply add_nonneg hl
      split
      · exact hk _ _
      · exact le_rfl

theorem gauss_nonneg (n : ℕ) (k : ℤ) (i : ℕ) : 0 ≤ (gauss n k).coeff i := by
  unfold gauss
  split
  · exact rect_nonneg ..
  · simp

/-- The source's denominator products use (q;q)_n. -/
def pochhammer (n : ℕ) : ℤ[X] := ∏ i ∈ Finset.range n, (1 - X ^ (i + 1))

theorem pochhammer_eq (n : ℕ) : pochhammer n = qFactorial n * (1-X)^n := by
  unfold pochhammer qFactorial
  simp_rw [← qInt_mul_one_sub, Finset.prod_mul_distrib]
  simp

theorem gauss_pochhammer {n k : ℕ} (h : k ≤ n) :
    gauss n k * (pochhammer k * pochhammer (n-k)) = pochhammer n := by
  simp only [pochhammer_eq]
  calc
    _ = (gauss n k * (qFactorial k * qFactorial (n-k))) * (1-X)^(k+(n-k)) := by
      rw [pow_add]
      ring
    _ = _ := by rw [gauss_factorial h, Nat.add_sub_of_le h]

theorem rect_symm (k l : ℕ) : rect k l = rect l k := by
  apply mul_right_cancel₀ (mul_ne_zero (qFactorial_monic k).ne_zero (qFactorial_monic l).ne_zero)
  rw [rect_factorial, mul_comm (qFactorial k), rect_factorial, add_comm]

theorem gauss_symm {n k : ℕ} (h : k ≤ n) : gauss n k = gauss n ((n-k : ℕ) : ℤ) := by
  rw [gauss_nat h, gauss_nat (Nat.sub_le n k), Nat.sub_sub_self h, rect_symm]

theorem rect_adjacent (k l : ℕ) :
    qInt (k+1) * rect (k+1) l = qInt (l+1) * rect k (l+1) := by
  apply mul_right_cancel₀ (mul_ne_zero (qFactorial_monic k).ne_zero (qFactorial_monic l).ne_zero)
  calc
    _ = rect (k+1) l * (qFactorial (k+1) * qFactorial l) := by rw [qFactorial_succ]; ring
    _ = rect k (l+1) * (qFactorial k * qFactorial (l+1)) := by
      rw [rect_factorial, rect_factorial]
      congr 1
      omega
    _ = _ := by rw [qFactorial_succ]; ring

theorem rect_lower (k l : ℕ) :
    qInt (k+1) * qInt (l+1) * rect (k+1) (l+1) =
      qInt (k+l+2) * qInt (k+l+1) * rect k l := by
  apply mul_right_cancel₀ (mul_ne_zero (qFactorial_monic k).ne_zero (qFactorial_monic l).ne_zero)
  calc
    _ = rect (k+1) (l+1) * (qFactorial (k+1) * qFactorial (l+1)) := by
      rw [qFactorial_succ, qFactorial_succ]
      ring
    _ = qFactorial (k+l+2) := by
      rw [rect_factorial]
      congr 1
      omega
    _ = _ := by
      rw [qFactorial_succ, qFactorial_succ]
      rw [← rect_factorial k l]
      ring

end Catalan
```

## CatalanStatement.lean

```lean
import QGaussian
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

abbrev LR := LaurentPolynomial ℤ
abbrev K := FractionRing LR

def embed : LR →+* K := algebraMap LR K

theorem embed_injective : Function.Injective embed :=
  IsFractionRing.injective LR K

def Nonnegative (L : LR) : Prop := ∀ z : ℤ, 0 ≤ L.coeff z

theorem nonnegative_zero : Nonnegative 0 := fun _ => le_rfl

theorem nonnegative_T (z : ℤ) : Nonnegative (T z) := fun i => by
  simp [T_apply, apply_ite]

theorem nonnegative_one : Nonnegative 1 := by
  simpa only [T_zero] using nonnegative_T 0

theorem Nonnegative.add {L M : LR} (hL : Nonnegative L) (hM : Nonnegative M) :
    Nonnegative (L + M) := fun z => add_nonneg (hL z) (hM z)

theorem Nonnegative.mul {L M : LR} (hL : Nonnegative L) (hM : Nonnegative M) :
    Nonnegative (L * M) := by
  intro z
  rw [AddMonoidAlgebra.coeff_mul]
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    change 0 ≤ if x + y = z then L.coeff x * M.coeff y else 0
    split
    · exact mul_nonneg (hL x) (hM y)
    · exact le_rfl

theorem Nonnegative.pow {L : LR} (hL : Nonnegative L) (n : ℕ) :
    Nonnegative (L ^ n) := by
  induction n with
  | zero => simpa using nonnegative_one
  | succ n ih => simpa only [pow_succ] using ih.mul hL

theorem nonnegative_sum {ι : Type*} (s : Finset ι) (f : ι → LR)
    (h : ∀ i ∈ s, Nonnegative (f i)) : Nonnegative (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nonnegative_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self ..)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem nonnegative_toLaurent {p : ℤ[X]} (h : ∀ i, 0 ≤ p.coeff i) :
    Nonnegative (toLaurent p) := by
  intro z
  rw [coeff_toLaurent]
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz]
    change 0 ≤ (Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ) p.toFinsupp.coeff)
      ((Nat.castEmbedding : ℕ ↪ ℤ) z.toNat)
    rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
    exact h _
  · have hnr : z ∉ Set.range (Nat.castEmbedding : ℕ ↪ ℤ) := by
      rintro ⟨i, hi⟩
      change (i : ℤ) = z at hi
      omega
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnr]

def qi (n : ℕ) : LR := toLaurent (qInt n)
def gb (n : ℕ) (k : ℤ) : LR := toLaurent (gauss n k)

theorem nonnegative_qi (n : ℕ) : Nonnegative (qi n) :=
  nonnegative_toLaurent (qInt_nonneg n)

theorem nonnegative_gb (n : ℕ) (k : ℤ) : Nonnegative (gb n k) :=
  nonnegative_toLaurent (gauss_nonneg n k)

theorem qi_ne_zero {n : ℕ} (hn : n ≠ 0) : qi n ≠ 0 :=
  toLaurent_ne_zero.mpr (qInt_monic hn).ne_zero

theorem gb_ne_zero {n k : ℕ} (h : k ≤ n) : gb n k ≠ 0 :=
  toLaurent_ne_zero.mpr (gauss_monic h).ne_zero

theorem nonnegative_invert {L : LR} (h : Nonnegative L) :
    Nonnegative (invert L) := fun z => by simpa using h (-z)

/-- Walk the adjacent pairs, with a closing edge from the last part to the first. -/
def edgesFrom (first current : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => [(current, first)]
  | next :: rest => (current, next) :: edgesFrom first next rest

def cyclicPairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs => edgesFrom x x xs

def first (ns : List ℕ) : ℕ := ns.headD 0
def last (ns : List ℕ) : ℕ := ns.getLastD 0

def cyclicWeight (ns : List ℕ) (k : ℕ) : LR :=
  ((cyclicPairs ns).map fun xy => gb (xy.1 + xy.2) ((xy.1 : ℤ) + k)).prod

def numerator (ns : List ℕ) (j : ℤ) (a r : ℕ) : LR :=
  ∑ k ∈ Finset.Icc a (first ns),
    qi (2 * k) * qi k ^ (2 * r) * T (j * (k : ℤ)^2 - ((r : ℤ) + 1) * k) *
      cyclicWeight ns k

def denominator (ns : List ℕ) (a : ℕ) : LR :=
  qi (last ns + a) * gb (first ns + last ns) ((first ns : ℤ) - a)

/-- Guo–Lian Conjecture 6.1's expression in the fraction field of ℤ[q,q⁻¹]. -/
def expression (ns : List ℕ) (j : ℤ) (a r : ℕ) : K :=
  (1 / embed (qi (last ns + a))) *
    (embed (gb (first ns + last ns) ((first ns : ℤ) - a)))⁻¹ *
    embed (numerator ns j a r)

theorem expression_eq_div (ns : List ℕ) (j : ℤ) (a r : ℕ) :
    expression ns j a r = embed (numerator ns j a r) / embed (denominator ns a) := by
  simp only [expression, denominator, map_mul, div_eq_mul_inv, one_mul, mul_inv_rev]
  ring

theorem denominator_ne_zero (ns : List ℕ) (hne : ns ≠ [])
    (hpos : ∀ n ∈ ns, 0 < n) {a : ℕ} (ha : a ≤ first ns) :
    denominator ns a ≠ 0 := by
  have hl : 0 < last ns := hpos _ (by
    unfold last
    cases ns with
    | nil => exact (hne rfl).elim
    | cons n ns => rw [List.getLastD_cons]; exact List.getLastD_mem_cons)
  unfold denominator
  rw [← Int.ofNat_sub ha]
  exact mul_ne_zero (qi_ne_zero (by omega)) (gb_ne_zero (by omega))

theorem expression_eq_embed_iff (ns : List ℕ) (j : ℤ) (a r : ℕ)
    (hD : denominator ns a ≠ 0) (L : LR) :
    expression ns j a r = embed L ↔ numerator ns j a r = L * denominator ns a := by
  rw [expression_eq_div, div_eq_iff, ← map_mul, embed_injective.eq_iff]
  exact fun h => (map_eq_zero_iff _ embed_injective).mp h |> hD

/-- Integer Laurentness for arbitrary j, together with the source's positivity range. -/
def GuoLianConjecture : Prop :=
  ∀ ns : List ℕ, ns ≠ [] → (∀ n ∈ ns, 0 < n) →
    ∀ (j : ℤ) (a r : ℕ), a ≤ first ns →
      ∃ L : LR, expression ns j a r = embed L ∧
        (0 ≤ j → j ≤ (ns.length : ℤ) → Nonnegative L)

#check qInt
#check gauss
#check gauss_pochhammer
#check gauss_nonneg
#check expression
#check GuoLianConjecture
#check expression_eq_embed_iff
#print axioms qInt
#print axioms gauss
#print axioms gauss_pochhammer
#print axioms gauss_nonneg
#print axioms expression
#print axioms GuoLianConjecture
#print axioms expression_eq_embed_iff

end Catalan
```

## CatalanMoments.lean

```lean
import CatalanStatement
import Mathlib.Algebra.BigOperators.Intervals

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

@[simp] theorem qi_zero : qi 0 = 0 := by simp [qi]
@[simp] theorem qi_one : qi 1 = 1 := by simp [qi]

theorem qi_add (x y : ℕ) : qi (x+y) = qi x + T (x : ℤ) * qi y := by
  simp [qi, qInt_add]

theorem qi_one_add (x : ℕ) : qi (1+x) = 1 + T 1 * qi x := by
  rw [qi_add]
  simp

theorem qi_mul_one_sub (n : ℕ) : qi n * (1-T 1) = 1-T (n : ℤ) := by
  simpa [qi] using congrArg (toLaurent (R := ℤ)) (qInt_mul_one_sub n)

def gr (k l : ℕ) : LR := toLaurent (rect k l)

@[simp] theorem gr_zero_left (l : ℕ) : gr 0 l = 1 := by simp [gr]
@[simp] theorem gr_zero_right (k : ℕ) : gr k 0 = 1 := by simp [gr]

theorem gb_rect (k l : ℕ) : gb (k+l) k = gr k l := by
  simp only [gb, gr, gauss_rect]

theorem gb_rect_of_add {n k l : ℕ} (h : n = k+l) : gb n k = gr k l := by
  subst n
  exact gb_rect k l

theorem gr_adjacent (k l : ℕ) :
    qi (k+1) * gr (k+1) l = qi (l+1) * gr k (l+1) := by
  simpa [qi, gr] using congrArg (toLaurent (R := ℤ)) (rect_adjacent k l)

theorem gr_lower (k l : ℕ) :
    qi (k+1) * qi (l+1) * gr (k+1) (l+1) =
      qi (k+l+2) * qi (k+l+1) * gr k l := by
  simpa [qi, gr] using congrArg (toLaurent (R := ℤ)) (rect_lower k l)

@[simp] theorem T_mul_T (i j : ℤ) : (T i : LR) * T j = T (i+j) :=
  (T_add i j).symm

/-- The moment variable q⁻ᵏ [k]². -/
def A (k : ℕ) : LR := T (-(k : ℤ)) * qi k ^ 2

theorem A_sub {n k : ℕ} (h : k ≤ n) :
    A n - A k = T (-(n : ℤ)) * qi (n-k) * qi (n+k) := by
  have h₁ : qi (n-k) + T ((n-k : ℕ) : ℤ) * qi k = qi n := by
    rw [← qi_add, Nat.sub_add_cancel h]
  have h₂ : qi k + T (k : ℤ) * qi (n-k) = qi n := by
    rw [← qi_add, Nat.add_comm, Nat.sub_add_cancel h]
  have h₃ : (T ((n-k : ℕ) : ℤ) : LR) * T (k : ℤ) = T (n : ℤ) := by
    rw [T_mul_T]
    congr 1
    omega
  have h₄ : (T (-(n : ℤ)) : LR) * T ((n-k : ℕ) : ℤ) = T (-(k : ℤ)) := by
    rw [T_mul_T]
    congr 1
    omega
  simp only [A, qi_add]
  calc
    _ = T (-(n : ℤ)) * (qi n ^ 2 - T ((n-k : ℕ) : ℤ) * qi k ^ 2) := by
      rw [mul_sub, ← mul_assoc, h₄]
    _ = T (-(n : ℤ)) *
        (qi n * (qi n - T ((n-k : ℕ) : ℤ) * qi k) +
          T ((n-k : ℕ) : ℤ) * qi k * (qi n - qi k)) := by ring
    _ = T (-(n : ℤ)) * qi (n-k) * (qi n + T (n : ℤ) * qi k) := by
      rw [show qi n - T ((n-k : ℕ) : ℤ) * qi k = qi (n-k) by rw [← h₁, add_sub_cancel_right],
        show qi n - qi k = T (k : ℤ) * qi (n-k) by rw [← h₂, add_sub_cancel_left], ← h₃]
      ring

def oneDenom (n a : ℕ) : LR := qi (n+a) * gr (n-a) (n+a)

def oneWeight (n t : ℕ) : LR := T (t : ℤ) * qi (2*(n-t)) * gb (2*n) t

def momentSum (n a r : ℕ) : LR :=
  ∑ t ∈ Finset.range (n-a+1), oneWeight n t * A (n-t) ^ r

private def boundary (n t : ℕ) : LR := qi t * gb (2*n) t

private theorem boundary_succ {n t : ℕ} (ht : t < 2*n) :
    boundary n (t+1) = qi (2*n-t) * gb (2*n) t := by
  unfold boundary
  rw [gb_rect_of_add (k := t+1) (l := 2*n-(t+1)) (by omega),
    gb_rect_of_add (k := t) (l := 2*n-t) (by omega),
    show 2*n-t = 2*n-(t+1)+1 by omega, gr_adjacent]

private theorem oneWeight_telescopes {n t : ℕ} (ht : t ≤ n) :
    oneWeight n t = boundary n (t+1) - boundary n t := by
  by_cases hn : n = 0
  · subst n
    have : t=0 := by omega
    subst t
    simp [oneWeight, boundary, gb, gauss_outside (n := 0) (k := 1) (by omega)]
  · rw [boundary_succ (by omega), boundary, oneWeight, ← sub_mul]
    congr 1
    rw [show 2*n-t = t + 2*(n-t) by omega, qi_add, add_sub_cancel_left]

theorem momentSum_zero {n a : ℕ} (ha : a ≤ n) :
    momentSum n a 0 = oneDenom n a := by
  unfold momentSum
  simp only [pow_zero, mul_one]
  calc
    _ = ∑ t ∈ Finset.range (n-a+1), (boundary n (t+1) - boundary n t) :=
      Finset.sum_congr rfl fun t ht =>
        oneWeight_telescopes (by have := Finset.mem_range.mp ht; omega)
    _ = boundary n (n-a+1) - boundary n 0 := Finset.sum_range_sub _ _
    _ = _ := by
      by_cases hn : n = 0
      · subst n
        have : a=0 := by omega
        subst a
        simp [boundary, oneDenom, gb, gauss_outside (n := 0) (k := 1) (by omega)]
      · rw [boundary_succ (by omega)]
        simp only [boundary, qi_zero, zero_mul, sub_zero, oneDenom]
        rw [show 2*n-(n-a) = n+a by omega, gb_rect_of_add (l := n+a) (by omega)]

theorem momentSum_boundary (a r : ℕ) :
    momentSum a a (r+1) = A a * momentSum a a r := by
  simp [momentSum, pow_succ', mul_left_comm]

private theorem oneWeight_lower {n t : ℕ} (ht : t < n+1) :
    (A (n+1) - A (n+1-(t+1))) * oneWeight (n+1) (t+1) =
      (T (-(n : ℤ)) * qi (2*(n+1)) * qi (2*n+1)) * oneWeight n t := by
  rw [A_sub (Nat.sub_le ..)]
  have h₁ : n+1-(t+1) = n-t := by omega
  have h₂ : n+1-(n-t) = t+1 := by omega
  have h₃ : n+1+(n-t) = (2*n-t)+1 := by omega
  rw [h₁,h₂,h₃, oneWeight, oneWeight, h₁,
    gb_rect_of_add (k := t+1) (l := (2*n-t)+1) (by omega),
    gb_rect_of_add (k := t) (l := 2*n-t) (by omega)]
  calc
    _ = (T (-(↑(n+1) : ℤ)) * T (↑(t+1) : ℤ)) * qi (2*(n-t)) *
          (qi (t+1) * qi (2*n-t+1) * gr (t+1) (2*n-t+1)) := by ring
    _ = _ := by
      rw [gr_lower, show t+(2*n-t)+2=2*(n+1) by omega,
        show t+(2*n-t)+1=2*n+1 by omega]
      rw [show (T (-(↑(n+1) : ℤ)) : LR) * T (↑(t+1) : ℤ) = T (-(n : ℤ)) * T (t : ℤ) by
        simp only [T_mul_T]; congr 1; omega]
      ring

theorem momentSum_step {n a : ℕ} (ha : a ≤ n) (r : ℕ) :
    A (n+1) * momentSum (n+1) a r - momentSum (n+1) a (r+1) =
      (T (-(n : ℤ)) * qi (2*(n+1)) * qi (2*n+1)) * momentSum n a r := by
  simp only [momentSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [show n+1-a+1=(n-a+1)+1 by omega]
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_succ', mul_left_comm (oneWeight _ _) (A _), sub_self, add_zero]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [Nat.add_sub_add_right, ← sub_mul]
  calc
    _ = ((A (n+1) - A (n+1-(t+1))) * oneWeight (n+1) (t+1)) * A (n-t)^r := by
      rw [Nat.add_sub_add_right]
      ring
    _ = _ := by rw [oneWeight_lower (by omega)]; ring

theorem oneDenom_step {n a : ℕ} (ha : a ≤ n) :
    qi (2*(n+1)) * qi (2*n+1) * oneDenom n a =
      qi (n+1-a) * qi (n+a) * oneDenom (n+1) a := by
  unfold oneDenom
  rw [show n+1-a=(n-a)+1 by omega, show n+1+a=(n+a)+1 by omega]
  calc
    _ = qi (n+a) *
        (qi ((n-a)+(n+a)+2) * qi ((n-a)+(n+a)+1) * gr (n-a) (n+a)) := by
      rw [show n-a+(n+a)+2=2*(n+1) by omega, show n-a+(n+a)+1=2*n+1 by omega]
      ring
    _ = _ := by rw [← gr_lower]; ring

end Catalan
```

## CatalanNewton.lean

```lean
import CatalanMoments
import Mathlib.Tactic.LinearCombination

open LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

private def falling (d i : ℕ) : LR :=
  ∏ s ∈ Finset.range i, qi (d-s)

private theorem falling_succ_index (d i : ℕ) :
    falling d (i+1) = falling d i * qi (d-i) := by
  simp [falling, Finset.prod_range_succ]

private theorem falling_succ_row (d i : ℕ) :
    falling (d+1) (i+1) = qi (d+1) * falling d i := by
  unfold falling
  rw [Finset.prod_range_succ']
  simp [Nat.add_sub_add_right, mul_comm]

/-- Evaluate the Newton basis at q⁻⁽ᵃ⁺ᵈ⁾. -/
def newton (a i d : ℕ) : LR := T (-(↑(a+d) : ℤ) * i) * falling d i

@[simp] theorem newton_zero_index (a d : ℕ) : newton a 0 d = 1 := by
  simp [newton, falling, T_zero]

theorem newton_succ (a i d : ℕ) :
    newton a (i+1) d = (T (-(↑(a+d) : ℤ)) * qi (d-i)) * newton a i d := by
  rw [newton, newton, falling_succ_index]
  rw [show (-(↑(a+d) : ℤ) * (↑(i+1) : ℤ)) = -(↑(a+d) : ℤ) + (-(↑(a+d) : ℤ) * i) by
    simp only [Nat.cast_add, Nat.cast_one]; ring, T_add]
  ring

theorem newton_vanishes {a i d : ℕ} (h : d < i) : newton a i d = 0 := by
  unfold newton falling
  rw [Finset.prod_eq_zero (Finset.mem_range.mpr h) (by simp)]
  exact mul_zero _

theorem newton_nonnegative (a i d : ℕ) : Nonnegative (newton a i d) := by
  induction i with
  | zero => simpa using nonnegative_one
  | succ i ih =>
    rw [newton_succ]
    exact ((nonnegative_T _).mul (nonnegative_qi _)).mul ih

private theorem newton_shift (a d i : ℕ) :
    qi (d+1) * newton a i d =
      T (i : ℤ) * qi (d+1-i) * newton a i (d+1) := by
  unfold newton
  rw [show (-(↑(a+d) : ℤ) * i) = (i : ℤ) + (-(↑(a+(d+1)) : ℤ) * i) by
    simp only [Nat.cast_add, Nat.cast_one]; ring, T_add]
  have h := falling_succ_row d i
  rw [falling_succ_index] at h
  calc
    _ = (T (i : ℤ) * T (-(↑(a+(d+1)) : ℤ) * i)) *
          (qi (d+1) * falling d i) := by ring
    _ = _ := by rw [← h]; ring

/-- The positive diagonal coefficient in the Newton action. -/
def diagonal (a i : ℕ) : LR :=
  A a + T (-(↑(a+i) : ℤ)) * qi i + T (1-↑(a+i)) * qi i * qi (2*a+i-1)

theorem diagonal_nonnegative (a i : ℕ) : Nonnegative (diagonal a i) :=
  (((nonnegative_T _).mul ((nonnegative_qi _).pow 2)).add
    ((nonnegative_T _).mul (nonnegative_qi _))).add
    (((nonnegative_T _).mul (nonnegative_qi _)).mul (nonnegative_qi _))

private theorem diagonal_zero_index (a : ℕ) : diagonal a 0 = A a := by simp [diagonal]

/-- The signed moment recurrence, indexed by the offset from the lower bound. -/
def momentOp (a : ℕ) (f : ℕ → LR) : ℕ → LR
  | 0 => A a * f 0
  | d+1 => A (a+(d+1)) * f (d+1) -
      T (1-↑(a+(d+1))) * qi (d+1) * qi (a+d+a) * f d

private theorem action_coefficient {a u i : ℕ} (hi : i ≤ u) (hu : 0 < u) :
    A (a+u) - T (1-↑(a+u)) * qi (a+u+a-1) * T (i : ℤ) * qi (u-i) =
      diagonal a i + qi (i+1) * (T (-(↑(a+u) : ℤ)) * qi (u-i)) := by
  have hd : qi u = qi i + T (i : ℤ) * qi (u-i) := by
    rw [← qi_add, Nat.add_sub_of_le hi]
  have hd' : qi u = qi (u-i) + T (↑(u-i) : ℤ) * qi i := by
    rw [← qi_add, Nat.sub_add_cancel hi]
  have hb : A (a+u) =
      A a + T (-(↑(a+u) : ℤ)) * qi u + T (1-↑(a+u)) * qi (a+u+a-1) * qi u := by
    have h := A_sub (n := a+u) (k := a) (by omega)
    rw [show a+u-a=u by omega, show a+u+a=1+(a+u+a-1) by omega, qi_one_add] at h
    rw [show (T (1-↑(a+u)) : LR) = T (-(↑(a+u) : ℤ)) * T 1 by
      simp only [T_mul_T]; congr 1; omega]
    linear_combination h
  have ht₁ : (T (-(↑(a+u) : ℤ)) : LR) * T (↑(u-i) : ℤ) = T (-(↑(a+i) : ℤ)) := by
    rw [T_mul_T]
    congr 1
    omega
  have ht₂ : (T (-(↑(a+u) : ℤ)) : LR) * T 1 = T (1-↑(a+u)) := by
    rw [T_mul_T]
    congr 1
    omega
  rw [hb]
  calc
    _ = A a + T (-(↑(a+u) : ℤ)) * qi u + T (1-↑(a+u)) * qi (a+u+a-1) * qi i := by
      rw [hd]
      ring
    _ = A a + T (-(↑(a+i) : ℤ)) * qi i + T (-(↑(a+u) : ℤ)) * qi (u-i) +
         T (1-↑(a+u)) * qi (a+u+a-1) * qi i := by
      rw [hd', ← ht₁]
      ring
    _ = _ := by
      by_cases h : i = 0
      · subst i
        simp [diagonal]
      · have hlen : a+u+a-1 = (u-i) + (2*a+i-1) := by omega
        have ht₃ : (T (1-↑(a+u)) : LR) * T (↑(u-i) : ℤ) = T (1-↑(a+i)) := by
          rw [T_mul_T]
          congr 1
          omega
        rw [diagonal, hlen, qi_add, show i+1 = 1+i by omega, qi_one_add, ← ht₂, ← ht₃, ← ht₂]
        ring

theorem newton_action (a i : ℕ) :
    momentOp a (newton a i) =
      fun d => diagonal a i * newton a i d + qi (i+1) * newton a (i+1) d := by
  funext d
  cases d with
  | zero =>
    cases i with
    | zero => simp [momentOp, diagonal_zero_index, newton_vanishes (show 0 < 1 by omega)]
    | succ i =>
      simp [momentOp, newton_vanishes (show 0 < i+1 by omega),
        newton_vanishes (show 0 < i+1+1 by omega)]
  | succ d =>
    by_cases hi : i ≤ d+1
    · simp only [momentOp]
      rw [show a+d+a = a+(d+1)+a-1 by omega]
      calc
        _ = A (a+(d+1)) * newton a i (d+1) -
            T (1-↑(a+(d+1))) * qi (a+(d+1)+a-1) * (qi (d+1) * newton a i d) := by ring
        _ = (A (a+(d+1)) - T (1-↑(a+(d+1))) * qi (a+(d+1)+a-1) *
              T (i : ℤ) * qi (d+1-i)) * newton a i (d+1) := by rw [newton_shift]; ring
        _ = _ := by rw [action_coefficient hi (by omega), newton_succ]; ring
    · have h₁ : d+1 < i := by omega
      have h₂ : d < i := by omega
      have h₃ : d+1 < i+1 := by omega
      simp [momentOp, newton_vanishes h₁, newton_vanishes h₂, newton_vanishes h₃]

/-- Finite linear combinations of the evaluated Newton basis with nonnegative coefficients. -/
inductive PositiveSpan (a : ℕ) : (ℕ → LR) → Prop
  | basis (i : ℕ) : PositiveSpan a (newton a i)
  | add {f g} : PositiveSpan a f → PositiveSpan a g → PositiveSpan a (fun n => f n + g n)
  | scale {c f} : Nonnegative c → PositiveSpan a f → PositiveSpan a (fun n => c * f n)

theorem PositiveSpan.nonnegative {a : ℕ} {f : ℕ → LR} (h : PositiveSpan a f) (d : ℕ) :
    Nonnegative (f d) := by
  induction h with
  | basis i => exact newton_nonnegative a i d
  | add _ _ hf hg => exact hf.add hg
  | scale hc _ hf => exact hc.mul hf

theorem PositiveSpan.closed_under_momentOp {a : ℕ} {f : ℕ → LR} (h : PositiveSpan a f) :
    PositiveSpan a (momentOp a f) := by
  induction h with
  | basis i =>
    rw [newton_action]
    exact .add (.scale (diagonal_nonnegative a i) (.basis i))
      (.scale (nonnegative_qi _) (.basis (i+1)))
  | add hf hg ihf ihg =>
    rename_i f g
    have hop : momentOp a (fun n => f n + g n) =
        fun n => momentOp a f n + momentOp a g n := by
      funext n
      cases n <;> simp only [momentOp] <;> ring
    rw [hop]
    exact .add ihf ihg
  | scale hc hf ihf =>
    rename_i c f
    have hop : momentOp a (fun n => c * f n) = fun n => c * momentOp a f n := by
      funext n
      cases n <;> simp only [momentOp] <;> ring
    rw [hop]
    exact .scale hc ihf

/-- Normalized one-part moments, with the regular extension to (a,n)=(0,0). -/
def moment (a : ℕ) : ℕ → ℕ → LR
  | 0 => fun _ => 1
  | r+1 => momentOp a (moment a r)

theorem moment_nonnegative (a r d : ℕ) : Nonnegative (moment a r d) := by
  suffices h : PositiveSpan a (moment a r) from h.nonnegative d
  induction r with
  | zero =>
    have h : moment a 0 = newton a 0 := by funext d; simp [moment]
    rw [h]
    exact .basis 0
  | succ r ih => exact ih.closed_under_momentOp

theorem moment_normalizes (a r d : ℕ) :
    oneDenom (a+d) a * moment a r d = momentSum (a+d) a r := by
  induction r generalizing d with
  | zero => simpa [moment] using (momentSum_zero (n := a+d) (a := a) (by omega)).symm
  | succ r ih =>
    cases d with
    | zero =>
      simp only [Nat.add_zero, moment, momentOp]
      rw [← mul_left_comm, show oneDenom a a * moment a r 0 = momentSum a a r by simpa using ih 0, momentSum_boundary]
    | succ d =>
      simp only [moment, momentOp]
      have h₁ := momentSum_step (n := a+d) (a := a) (by omega) r
      have h₂ := oneDenom_step (n := a+d) (a := a) (by omega)
      have h₃ : (T (1-↑(a+(d+1))) : LR) = T (-(↑(a+d) : ℤ)) := by congr 1; omega
      have h₄ : a+d+1-a = d+1 := by omega
      rw [h₄] at h₂
      rw [show a+(d+1) = a+d+1 by omega] at h₃ ⊢
      rw [h₃]
      calc
        _ = A (a+d+1) * (oneDenom (a+d+1) a * moment a r (d+1)) -
            T (-(↑(a+d) : ℤ)) *
              (qi (d+1) * qi (a+d+a) * oneDenom (a+d+1) a) * moment a r d := by ring
        _ = _ := by
          rw [show a+d+1=a+(d+1) by omega, ih (d+1), ← Nat.add_assoc, ← h₂]
          rw [← mul_assoc (T (-↑(a+d))), mul_assoc _ (oneDenom (a+d) a), ih d]
          linear_combination h₁

end Catalan
```

## CatalanOne.lean

```lean
import CatalanNewton

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

theorem oneDenom_literal {n a : ℕ} (ha : a ≤ n) :
    denominator [n] a = oneDenom n a := by
  change qi (n+a) * gb (n+n) ((n : ℤ)-a) = _
  rw [← Int.ofNat_sub ha, oneDenom, gb_rect_of_add (l := n+a) (by omega)]

/-- Reindex the singleton sum by t = n-k and normalize it by q^n. -/
def phasedMoment (n : ℕ) (j : ℤ) (a r : ℕ) : LR :=
  ∑ t ∈ Finset.range (n-a+1), oneWeight n t * A (n-t)^r * T (j * (↑(n-t) : ℤ)^2)

@[simp] theorem phasedMoment_zero (n a r : ℕ) :
    phasedMoment n 0 a r = momentSum n a r := by
  simp [phasedMoment, momentSum, T_zero]

theorem oneNumer_literal {n a : ℕ} (ha : a ≤ n) (j : ℤ) (r : ℕ) :
    T (n : ℤ) * numerator [n] j a r = phasedMoment n j a r := by
  unfold numerator phasedMoment
  rw [Finset.mul_sum]
  change (∑ k ∈ Finset.Icc a n, _) = _
  refine Finset.sum_bij' (fun k _ => n-k) (fun t _ => n-t) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hkn : k ≤ n := hk.2
    simp only [oneWeight, Nat.sub_sub_self hkn, cyclicWeight, cyclicPairs, edgesFrom,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, A, mul_pow, T_pow,
      ← pow_mul]
    have hgb : gb (n+n) ((n : ℤ)+k) = gb (2*n) (↑(n-k) : ℤ) := by
      rw [← Nat.cast_add, gb, gauss_symm (show n+k ≤ n+n by omega)]
      rw [show n+n-(n+k)=n-k by omega, show n+n=2*n by omega]
      rfl
    rw [hgb]
    calc
      _ = (T (n : ℤ) * T (j * (k : ℤ)^2 - ((r : ℤ)+1) * k)) *
          (qi (2*k) * qi k^(2*r) * gb (2*n) (↑(n-k) : ℤ)) := by ring
      _ = (T ((n-k : ℕ) : ℤ) * T ((r : ℤ) * -(k : ℤ)) * T (j * (k : ℤ)^2)) *
          (qi (2*k) * qi k^(2*r) * gb (2*n) (↑(n-k) : ℤ)) := by
        simp only [T_mul_T, Int.ofNat_sub hkn]
        congr 2
        ring
      _ = _ := by ring

theorem singleton_zero_phase {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) (r : ℕ) :
    ∃ L : LR, expression [n] 0 a r = embed L ∧ Nonnegative L := by
  refine ⟨T (-(n : ℤ)) * moment a r (n-a), ?_,
    (nonnegative_T _).mul (moment_nonnegative a r (n-a))⟩
  have hD := denominator_ne_zero [n] (by simp) (by simpa using hn) ha
  rw [expression_eq_embed_iff _ _ _ _ hD, oneDenom_literal ha]
  have hz := moment_normalizes a r (n-a)
  rw [Nat.add_sub_of_le ha] at hz
  have h := oneNumer_literal ha 0 r
  rw [phasedMoment_zero, ← hz] at h
  calc
    _ = T (-(n : ℤ)) * (T (n : ℤ) * numerator [n] 0 a r) := by
      simp only [← mul_assoc, T_mul_T, neg_add_cancel, T_zero, one_mul]
    _ = _ := by rw [h]; ring

#check singleton_zero_phase
#print axioms singleton_zero_phase

end Catalan
```

## CatalanDenomRoots.lean

```lean
import CatalanOne
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.OrderOfElement

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

/-- The singleton denominator before embedding ordinary polynomials in the Laurent ring. -/
def oneDenomPoly (n a : ℕ) : ℤ[X] := qInt (n+a) * rect (n-a) (n+a)

theorem oneDenom_toLaurent (n a : ℕ) : toLaurent (oneDenomPoly n a) = oneDenom n a := by
  simp [oneDenomPoly, oneDenom, qi, gr]

theorem oneDenomPoly_monic {n a : ℕ} (hn : 0 < n) : (oneDenomPoly n a).Monic :=
  (qInt_monic (by omega)).mul (rect_monic _ _)

theorem oneDenomPoly_factorial {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) :
    oneDenomPoly n a * (qFactorial (n-a) * qFactorial (n+a-1)) = qFactorial (2*n) := by
  calc
    _ = rect (n-a) (n+a) * (qFactorial (n-a) * qFactorial (n+a)) := by
      unfold oneDenomPoly
      rw [show qFactorial (n+a) = qFactorial (n+a-1) * qInt (n+a) by
        simpa only [show (n+a-1)+1 = n+a by omega] using qFactorial_succ (n+a-1)]
      ring
    _ = _ := by rw [rect_factorial, show n-a+(n+a)=2*n by omega]

private abbrev intComplex : ℤ →+* ℂ := Int.castRingHom ℂ
local notation "cpoly" => Polynomial.map intComplex

private theorem eval_qInt_zero {s : ℕ} (hs : s ≠ 0) :
    (cpoly (qInt s)).eval 0 = 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  rw [Nat.succ_eq_add_one, Nat.add_comm, qInt_add]
  simp

private theorem eval_qInt_one (s : ℕ) :
    (cpoly (qInt s)).eval 1 = (s : ℂ) := by
  simp [qInt, eval_finsetSum]

private theorem eval_factorial_zero (s : ℕ) : (cpoly (qFactorial s)).eval 0 = 1 := by
  induction s with
  | zero => simp
  | succ s ih => simp [qFactorial_succ, ih, eval_qInt_zero (by omega : s+1 ≠ 0)]

private theorem eval_factorial_one (s : ℕ) : (cpoly (qFactorial s)).eval 1 ≠ 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [qFactorial_succ, Polynomial.map_mul, eval_mul, eval_qInt_one]
    exact mul_ne_zero ih (Nat.cast_ne_zero.mpr (by omega))

private theorem isRoot_of_denom_factorial {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) {ζ : ℂ}
    (h : IsRoot (cpoly (oneDenomPoly n a)) ζ) : IsRoot (cpoly (qFactorial (2*n))) ζ := by
  rw [← oneDenomPoly_factorial hn ha, Polynomial.map_mul, IsRoot, eval_mul]
  rw [show (cpoly (oneDenomPoly n a)).eval ζ = 0 from h, zero_mul]

theorem oneDenomPoly_root_ne_zero {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) {ζ : ℂ}
    (h : IsRoot (cpoly (oneDenomPoly n a)) ζ) : ζ ≠ 0 := by
  rintro rfl
  have h' := isRoot_of_denom_factorial hn ha h
  rw [IsRoot, eval_factorial_zero] at h'
  exact one_ne_zero h'

theorem oneDenomPoly_root_ne_one {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) {ζ : ℂ}
    (h : IsRoot (cpoly (oneDenomPoly n a)) ζ) : ζ ≠ 1 := by
  rintro rfl
  exact eval_factorial_one _ (isRoot_of_denom_factorial hn ha h)

private theorem qIntC_mul_X_sub_one (s : ℕ) :
    cpoly (qInt s) * (X-1) = X^s-1 := by
  simpa [qInt, Polynomial.map_sum] using geom_sum_mul (X : ℂ[X]) s

private theorem qi_rootMultiplicity {ζ : ℂ} (hz : ζ ≠ 1) {s : ℕ} (hs : s ≠ 0) :
    rootMultiplicity ζ (cpoly (qInt s)) = if orderOf ζ ∣ s then 1 else 0 := by
  have h := qIntC_mul_X_sub_one s
  have hno : ¬ IsRoot (X-1 : ℂ[X]) ζ := by simpa [IsRoot, sub_eq_zero] using hz
  have hne : cpoly (qInt s) * (X-1) ≠ 0 :=
    mul_ne_zero ((qInt_monic hs).map intComplex).ne_zero (by simpa using X_sub_C_ne_zero (1 : ℂ))
  have hm := congrArg (rootMultiplicity ζ) h
  rw [rootMultiplicity_mul hne, rootMultiplicity_eq_zero hno, add_zero] at hm
  rw [hm]
  by_cases hd : orderOf ζ ∣ s
  · rw [ite_eq_left hd]
    have hroot : IsRoot (X^s-1 : ℂ[X]) ζ := by
      simp [IsRoot, (orderOf_dvd_iff_pow_eq_one.mp hd)]
    have hsep : Separable (X^s-1 : ℂ[X]) := by
      simpa using separable_X_pow_sub_C (1 : ℂ) (Nat.cast_ne_zero.mpr hs) one_ne_zero
    have hpos := (rootMultiplicity_pos (h ▸ hne)).2 hroot
    have hle := rootMultiplicity_le_one_of_separable hsep ζ
    omega
  · rw [ite_eq_right hd]
    apply rootMultiplicity_eq_zero
    simpa [IsRoot, sub_eq_zero, ← orderOf_dvd_iff_pow_eq_one] using hd

private theorem factorial_rootMultiplicity {ζ : ℂ} (hz : ζ ≠ 1) (s : ℕ) :
    rootMultiplicity ζ (cpoly (qFactorial s)) = s / orderOf ζ := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [qFactorial_succ, Polynomial.map_mul,
      rootMultiplicity_mul (mul_ne_zero ((qFactorial_monic s).map intComplex).ne_zero
        ((qInt_monic (by omega : s+1 ≠ 0)).map intComplex).ne_zero),
      ih, qi_rootMultiplicity hz (by omega), Nat.succ_div]

/-- The carry in the factorial multiplicity formula is at most one. -/
private theorem single_carry (b c d : ℕ) :
    (b+c+1)/d ≤ b/d + c/d + 1 := by
  by_cases hd : d=0
  · simp [hd]
  · suffices h : (b+c+1)/d < b/d+c/d+2 by omega
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm (b/d), Nat.mul_comm (c/d), two_mul]
    have hb := Nat.mod_add_div b d
    have hc := Nat.mod_add_div c d
    have hb' := Nat.mod_lt b (by omega : 0 < d)
    have hc' := Nat.mod_lt c (by omega : 0 < d)
    omega

/-- Every root of the normalized one-part denominator has multiplicity at most one. -/
theorem oneDenomPoly_rootMultiplicity_le_one {n a : ℕ} (hn : 0 < n) (ha : a ≤ n)
    (ζ : ℂ) : rootMultiplicity ζ (cpoly (oneDenomPoly n a)) ≤ 1 := by
  by_cases h : IsRoot (cpoly (oneDenomPoly n a)) ζ
  · have hne := oneDenomPoly_root_ne_one hn ha h
    have hmul := congrArg (fun p : ℤ[X] => rootMultiplicity ζ (cpoly p))
      (oneDenomPoly_factorial hn ha)
    simp only [Polynomial.map_mul] at hmul
    have h₁ := ((oneDenomPoly_monic (a := a) hn).map intComplex).ne_zero
    have h₂ := ((qFactorial_monic (n-a)).map intComplex).ne_zero
    have h₃ := ((qFactorial_monic (n+a-1)).map intComplex).ne_zero
    rw [rootMultiplicity_mul (mul_ne_zero h₁ (mul_ne_zero h₂ h₃)),
      rootMultiplicity_mul (mul_ne_zero h₂ h₃), factorial_rootMultiplicity hne,
      factorial_rootMultiplicity hne, factorial_rootMultiplicity hne] at hmul
    have hle := single_carry (n-a) (n+a-1) (orderOf ζ)
    rw [show n-a+(n+a-1)+1=2*n by omega] at hle
    omega
  · rw [rootMultiplicity_eq_zero h]
    exact Nat.zero_le _

end Catalan
```

## CatalanInterpolation.lean

```lean
import CatalanDenomRoots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

local notation "intComplex" => Int.castRingHom ℂ
local notation "cpoly" => Polynomial.map intComplex

private def evalL (ζ : ℂ) (hz : ζ ≠ 0) : LR →+* ℂ :=
  LaurentPolynomial.eval₂ intComplex (Units.mk0 ζ hz)

@[simp] private theorem evalL_T (ζ : ℂ) (hz : ζ ≠ 0) (i : ℤ) :
    evalL ζ hz (T i) = ζ ^ i := by
  simp [evalL, eval₂_T, Units.val_zpow_eq_zpow_val]

private theorem evalL_toLaurent (ζ : ℂ) (hz : ζ ≠ 0) (p : ℤ[X]) :
    evalL ζ hz (toLaurent p) = (cpoly p).eval ζ := by
  rw [evalL, eval₂_toLaurent, eval_map]
  rfl

private theorem evalA_scale {ζ : ℂ} (hz : ζ ≠ 0) (k : ℕ) :
    evalL ζ hz (A k) * (1-ζ)^2 * ζ^(k : ℤ) = (1-ζ^(k : ℤ))^2 := by
  have hq := congrArg (evalL ζ hz) (qi_mul_one_sub k)
  simp only [map_mul, map_sub, map_one, evalL_T, zpow_one] at hq
  simp only [A, map_mul, map_pow, evalL_T, zpow_neg]
  have hk : ζ^(k : ℤ) ≠ 0 := zpow_ne_zero _ hz
  calc
    _ = (ζ^(k : ℤ))⁻¹ * ζ^(k : ℤ) * (evalL ζ hz (qi k) * (1-ζ))^2 := by ring
    _ = _ := by rw [inv_mul_cancel₀ hk, one_mul, hq]

/-- The square phase is constant on the fibers of the moment variable. -/
private theorem phase_factors {ζ : ℂ} (hz : ζ ≠ 0) {k l : ℕ}
    (h : evalL ζ hz (A k) = evalL ζ hz (A l)) (j : ℤ) :
    ζ ^ (j*(k : ℤ)^2) = ζ ^ (j*(l : ℤ)^2) := by
  have hclin : (ζ^(k : ℤ) - ζ^(l : ℤ)) * (ζ^(k : ℤ) * ζ^(l : ℤ)-1) = 0 := by
    calc
      _ = ζ^(l : ℤ) * (1-ζ^(k : ℤ))^2 - ζ^(k : ℤ) * (1-ζ^(l : ℤ))^2 := by ring
      _ = _ := by rw [← evalA_scale hz k, ← evalA_scale hz l, h]; ring
  apply (div_eq_one_iff_eq (zpow_ne_zero _ hz)).mp
  rw [← zpow_sub₀ hz]
  rcases mul_eq_zero.mp hclin with h' | h'
  · have hp : ζ^((k : ℤ)-(l : ℤ)) = 1 := by
      rw [zpow_sub₀ hz, sub_eq_zero.mp h', div_self (zpow_ne_zero _ hz)]
    rw [show j*(k : ℤ)^2-j*(l : ℤ)^2=((k : ℤ)-(l : ℤ))*(j*((k : ℤ)+(l : ℤ))) by ring,
      zpow_mul, hp, one_zpow]
  · have hp : ζ^((k : ℤ)+(l : ℤ)) = 1 := by
      rw [zpow_add₀ hz, sub_eq_zero.mp h']
    rw [show j*(k : ℤ)^2-j*(l : ℤ)^2=((k : ℤ)+(l : ℤ))*(j*((k : ℤ)-(l : ℤ))) by ring,
      zpow_mul, hp, one_zpow]

private theorem eval_linear_moments {ι : Type*} (s : Finset ι) (w v : ι → ℂ)
    (h : ∀ b : ℕ, ∑ i ∈ s, w i * v i ^ b = 0) (r : ℕ) (P : ℂ[X]) :
    ∑ i ∈ s, w i * v i ^ r * P.eval (v i) = 0 := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp [eval_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | monomial k c =>
    calc
      _ = c * ∑ i ∈ s, w i * v i ^ (r+k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eval_monomial, pow_add]
        ring
      _ = _ := by rw [h, mul_zero]

private theorem phasedMoment_vanishes {n a : ℕ} (_hn : 0 < n) (ha : a ≤ n)
    {ζ : ℂ} (hz : ζ ≠ 0) (hroot : IsRoot (cpoly (oneDenomPoly n a)) ζ)
    (j : ℤ) (r : ℕ) : evalL ζ hz (phasedMoment n j a r) = 0 := by
  classical
  let s := Finset.range (n-a+1)
  let v : ℕ → ℂ := fun t => evalL ζ hz (A (n-t))
  let w : ℕ → ℂ := fun t => evalL ζ hz (oneWeight n t)
  let phase : ℕ → ℂ := fun t => ζ ^ (j*(↑(n-t) : ℤ)^2)
  have h : ∀ b : ℕ, ∑ t ∈ s, w t * v t ^ b = 0 := by
    intro b
    have hm := moment_normalizes a b (n-a)
    rw [Nat.add_sub_of_le ha] at hm
    have he := congrArg (evalL ζ hz) hm
    rw [← oneDenom_toLaurent, map_mul, evalL_toLaurent, show (cpoly (oneDenomPoly n a)).eval ζ = 0 from hroot, zero_mul] at he
    simpa only [momentSum, map_sum, map_mul, map_pow, s, w, v] using he.symm
  let value : ℂ → ℂ := fun u =>
    if hu : ∃ t ∈ s, v t = u then phase (Classical.choose hu) else 0
  let P := Lagrange.interpolate (s.image v) id value
  have hp : ∀ t ∈ s, P.eval (v t) = phase t := by
    intro t ht
    have hmem := Finset.mem_image_of_mem v ht
    have hex : ∃ i ∈ s, v i = v t := ⟨t, ht, rfl⟩
    have hi := (Classical.choose_spec hex).2
    have hi' : phase (Classical.choose hex) = phase t := phase_factors hz hi j
    calc
      _ = value (v t) := Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => h) hmem
      _ = _ := by simp only [value, dite_eq_left hex, hi']
  unfold phasedMoment
  simp only [map_sum, map_mul, map_pow, evalL_T]
  change (∑ t ∈ s, w t * v t ^ r * phase t) = 0
  rw [Finset.sum_congr rfl (fun t ht => congrArg (fun x => w t * v t ^ r * x) (hp t ht).symm)]
  exact eval_linear_moments s w v h r P

private theorem oneDenom_dvd_of_vanishes {n a : ℕ} (hn : 0 < n) (ha : a ≤ n)
    (N : LR) (h : ∀ ζ (hz : ζ ≠ 0), IsRoot (cpoly (oneDenomPoly n a)) ζ → evalL ζ hz N = 0) :
    oneDenom n a ∣ N := by
  obtain ⟨d, p, hp⟩ := exists_T_pow N
  have hmonic := oneDenomPoly_monic (a := a) hn
  have hdvd : oneDenomPoly n a ∣ p := by
    apply (map_dvd_map intComplex Int.cast_injective hmonic).mp
    by_cases hp0 : cpoly p = 0
    · simp [hp0]
    rw [IsAlgClosed.dvd_iff_roots_le_roots (hmonic.map intComplex).ne_zero hp0,
      Multiset.le_iff_count]
    intro ζ
    simp only [count_roots]
    by_cases hr : IsRoot (cpoly (oneDenomPoly n a)) ζ
    · have hz := oneDenomPoly_root_ne_zero hn ha hr
      have he := congrArg (evalL ζ hz) hp
      rw [evalL_toLaurent, map_mul, h ζ hz hr, zero_mul] at he
      exact (oneDenomPoly_rootMultiplicity_le_one hn ha ζ).trans
        (Nat.one_le_iff_ne_zero.mpr ((rootMultiplicity_pos hp0).mpr he).ne')
    · rw [rootMultiplicity_eq_zero hr]
      exact Nat.zero_le _
  obtain ⟨P, hP⟩ := hdvd
  rw [hP, map_mul, oneDenom_toLaurent] at hp
  refine ⟨toLaurent P * T (-(d : ℤ)), ?_⟩
  calc
    N = (N * T (d : ℤ)) * T (-(d : ℤ)) := by
      simp only [mul_assoc, T_mul_T, add_neg_cancel, T_zero, mul_one]
    _ = _ := by rw [← hp, mul_assoc]

theorem singleton_integral {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) (j : ℤ) (r : ℕ) :
    ∃ L : LR, expression [n] j a r = embed L := by
  have hD := denominator_ne_zero [n] (by simp) (by simpa using hn) ha
  obtain ⟨L, hL⟩ := oneDenom_dvd_of_vanishes hn ha (phasedMoment n j a r)
    (fun _ hz hr => phasedMoment_vanishes hn ha hz hr j r)
  refine ⟨T (-(n : ℤ)) * L, ?_⟩
  rw [expression_eq_embed_iff _ _ _ _ hD, oneDenom_literal ha]
  rw [← oneNumer_literal ha] at hL
  calc
    _ = T (-(n : ℤ)) * (T (n : ℤ) * numerator [n] j a r) := by
      simp only [← mul_assoc, T_mul_T, neg_add_cancel, T_zero, one_mul]
    _ = _ := by rw [hL]; ring

#check singleton_integral
#print axioms singleton_integral

end Catalan
```

## QChu.lean

```lean
import QGaussian
import Mathlib.Data.Nat.Choose.Sum

open Polynomial
open scoped BigOperators

noncomputable section

namespace Catalan

@[simp] theorem gauss_zero_col (n : ℕ) : gauss n 0 = 1 := by
  simpa using gauss_nat (Nat.zero_le n)

@[simp] theorem gauss_diag (n : ℕ) : gauss n (n : ℤ) = 1 := by
  simp [gauss_nat]

theorem gauss_succ_succ (n k : ℕ) :
    gauss (n+1) (↑(k+1) : ℤ) = gauss n (↑(k+1) : ℤ) + X^(n-k) * gauss n (k : ℤ) := by
  rcases lt_trichotomy k n with h | rfl | h
  · rw [gauss_nat (show k+1 ≤ n+1 by omega), gauss_nat (show k+1 ≤ n by omega),
      gauss_nat (show k ≤ n by omega)]
    obtain ⟨l, hl⟩ : ∃ l, n-k = l+1 := ⟨n-k-1, by omega⟩
    rw [show n+1-(k+1) = l+1 by omega, show n-(k+1)=l by omega, hl, rect_succ_succ]
  · rw [gauss_diag, gauss_outside (n := k) (k := (↑(k+1) : ℤ)) (by omega)]
    simp
  · rw [gauss_outside (n := n+1) (k := (↑(k+1) : ℤ)) (by omega),
      gauss_outside (n := n) (k := (↑(k+1) : ℤ)) (by omega),
      gauss_outside (n := n) (k := (k : ℤ)) (by omega), mul_zero, add_zero]

private def triangular : ℕ → ℕ
  | 0 => 0
  | k+1 => triangular k + k

private theorem triangular_add (i j : ℕ) :
    triangular (i+j) = triangular i + triangular j + i*j := by
  induction j with
  | zero => simp [triangular]
  | succ j ih =>
    rw [Nat.add_succ, triangular, triangular, ih, Nat.mul_succ]
    omega

/-- The coefficient variable is the outer polynomial variable. -/
private def gen (o n : ℕ) : ℤ[X][X] :=
  ∏ i ∈ Finset.range n, (1 + C ((X : ℤ[X])^(o+i)) * X)

private theorem gen_coeff (o n k : ℕ) :
    (gen o n).coeff k = (X : ℤ[X])^(o*k+triangular k) * gauss n (k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [gen, triangular]
    | succ k =>
      rw [gauss_outside (n := 0) (k := (↑(k+1) : ℤ)) (by omega)]
      simp [gen, coeff_one]
  | succ n ih =>
    have hgen : gen o (n+1) = gen o n * (1 + C ((X : ℤ[X])^(o+n)) * X) := by
      simp [gen, Finset.prod_range_succ]
    rw [hgen, mul_add, mul_one, ← mul_assoc, coeff_add]
    cases k with
    | zero => simp [ih, triangular]
    | succ k =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih, gauss_succ_succ, mul_add ((X : ℤ[X])^(o*(k+1)+triangular (k+1))) _ _]
      by_cases hk : k ≤ n
      · have he : o*(k+1)+triangular (k+1)+(n-k) =
            (o*k+triangular k)+(o+n) := by
          rw [triangular, Nat.mul_succ]
          omega
        congr 1
        calc
          (X : ℤ[X])^(o*k+triangular k) * gauss n (k : ℤ) * X^(o+n)
              = X^((o*k+triangular k)+(o+n)) * gauss n (k : ℤ) := by
                rw [pow_add]
                ring
          _ = _ := by rw [← he, pow_add, mul_assoc]
      · rw [gauss_outside (n := n) (k := (k : ℤ)) (by omega)]
        simp

private theorem gen_split (o u v : ℕ) : gen o (u+v) = gen o u * gen (o+u) v := by
  unfold gen
  rw [Finset.prod_range_add]
  simp only [Nat.add_assoc]

private theorem chu_filtered (u v k : ℕ) :
    gauss (u+v) (k : ℤ) =
      ∑ p ∈ (Finset.antidiagonal k).filter (fun p => p.1 ≤ u ∧ p.2 ≤ v),
        (X : ℤ[X])^((u-p.1)*p.2) * gauss u (p.1 : ℤ) * gauss v (p.2 : ℤ) := by
  apply mul_left_cancel₀ (pow_ne_zero (triangular k) X_ne_zero)
  have h := congrArg (fun p : ℤ[X][X] => p.coeff k) (gen_split 0 u v)
  change (gen 0 (u+v)).coeff k = (gen 0 u * gen (0+u) v).coeff k at h
  rw [coeff_mul, gen_coeff] at h
  simp only [gen_coeff, zero_add, zero_mul] at h
  rw [h, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum := Finset.mem_antidiagonal.mp hp
  split
  · rename_i hle
    rw [← hsum, triangular_add]
    have hexp : triangular p.1 + (u*p.2+triangular p.2) =
        (triangular p.1+triangular p.2+p.1*p.2)+(u-p.1)*p.2 := by
      rw [Nat.sub_mul]
      have hmul := Nat.mul_le_mul_right p.2 hle.1
      omega
    calc
      _ = (X : ℤ[X])^(triangular p.1 + (u*p.2+triangular p.2)) *
          (gauss u (p.1 : ℤ) * gauss v (p.2 : ℤ)) := by rw [pow_add]; ring
      _ = _ := by rw [hexp, pow_add]; ring
  · rename_i hn
    by_cases hpu : p.1 ≤ u
    · rw [gauss_outside (n := v) (k := (p.2 : ℤ)) (by omega), mul_zero, mul_zero]
    · rw [gauss_outside (n := u) (k := (p.1 : ℤ)) (by omega), mul_zero, zero_mul]

theorem qChu {x y k : ℕ} (hx : k ≤ x) (hy : k ≤ y) :
    gauss (x+y) (↑(x+k) : ℤ) =
      ∑ l ∈ Finset.Icc k (min x y),
        (X : ℤ[X])^(l*l-k*k) * gauss (x-k) (↑(l-k) : ℤ) * gauss (y+k) (↑(l+k) : ℤ) := by
  rw [show x+y = (x-k)+(y+k) by omega, chu_filtered]
  refine Finset.sum_bij' (fun p _ => p.2-k) (fun l _ => (x-l,l+k)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_Icc, le_min_iff] at hp ⊢
    omega
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_Icc, le_min_iff] at hl ⊢
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    ext <;> simp <;> omega
  · intro l hl
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    have he : x-k-p.1=p.2-k-k := by omega
    have h₁ : p.2-k+k=p.2 := by omega
    rw [he, h₁]
    have hpow : (p.2-k-k)*p.2 = (p.2-k)*(p.2-k)-k*k := by
      have heq : p.2 = (p.2-k-k)+k+k := by omega
      have heq' : p.2-k=(p.2-k-k)+k := by omega
      generalize hd : p.2-k-k = d at heq heq' ⊢
      apply Nat.eq_sub_of_add_eq
      rw [heq', heq]
      ring
    rw [hpow, show p.2-k-k=x-k-p.1 by omega]
    rw [gauss_symm hp.2.1]

#check qChu
#print axioms qChu

end Catalan
```

## CatalanFactorials.lean

```lean
import CatalanOne
import QChu
import Mathlib.Tactic.FieldSimp

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

def fact (n : ℕ) : K := embed (toLaurent (qFactorial n))

theorem fact_ne_zero (n : ℕ) : fact n ≠ 0 := by
  unfold fact
  exact fun h => (qFactorial_monic n).ne_zero
    (toLaurent_injective (embed_injective (h.trans (map_zero embed).symm)))

theorem fact_succ (n : ℕ) : fact (n+1) = fact n * embed (qi (n+1)) := by
  simp [fact, qi, qFactorial_succ]

theorem gauss_fraction {n k : ℕ} (hk : k ≤ n) :
    embed (gb n (k : ℤ)) = fact n / (fact k * fact (n-k)) := by
  apply (eq_div_iff (mul_ne_zero (fact_ne_zero _) (fact_ne_zero _))).2
  simpa only [gb, fact, map_mul] using
    congrArg (fun p : ℤ[X] => embed (toLaurent p)) (gauss_factorial hk)

theorem gauss_fraction_rect (k l : ℕ) :
    embed (gr k l) = fact (k+l) / (fact k * fact l) := by
  rw [← gb_rect, gauss_fraction (Nat.le_add_right k l), Nat.add_sub_cancel_left]

theorem gb_outside {n : ℕ} {k : ℤ} (hk : (n : ℤ) < k) : gb n k = 0 := by
  simp [gb, gauss_outside (Or.inr hk)]

def mono (z : ℤ) : K := embed (T z)

theorem mono_mul (x y : ℤ) : mono x * mono y = mono (x+y) := by
  unfold mono
  rw [← map_mul, T_mul_T]

/-- Inverse factorial factors from the two cyclic edges incident to a part. -/
def upperInv (n k : ℕ) : K := (fact (n+k))⁻¹

def lowerInv (n k : ℕ) : K := if k ≤ n then (fact (n-k))⁻¹ else 0

def kernel (n k : ℕ) : K := upperInv n k * lowerInv n k

theorem kernel_outside {n k : ℕ} (h : n < k) : kernel n k = 0 := by
  simp [kernel, lowerInv, Nat.not_le.mpr h]

theorem kernel_inside {n k : ℕ} (h : k ≤ n) :
    kernel n k = (fact (n+k))⁻¹ * (fact (n-k))⁻¹ := by
  simp [kernel, upperInv, lowerInv, h]

theorem edge_factorization (x y k : ℕ) :
    embed (gb (x+y) ((x : ℤ)+k)) = fact (x+y) * upperInv x k * lowerInv y k := by
  by_cases h : k ≤ y
  · rw [← Nat.cast_add, gauss_fraction (by omega : x+k ≤ x+y), show x+y-(x+k)=y-k by omega]
    simp only [lowerInv, ite_eq_left h, upperInv]
    field_simp [fact_ne_zero]
  · simp [gb_outside (by omega : ((x+y : ℕ) : ℤ) < (x : ℤ)+k), lowerInv, h]

/-- Factors attached to all edges other than the closing edge. -/
def openFact (current : ℕ) : List ℕ → K
  | [] => 1
  | y::ys => fact (current+y) * openFact y ys

def tailKernel (ns : List ℕ) (k : ℕ) : K :=
  (ns.map fun n => kernel n k).prod

private theorem walk_factorization (first current : ℕ) (xs : List ℕ) (k : ℕ) :
    embed (((edgesFrom first current xs).map fun xy => gb (xy.1+xy.2) ((xy.1 : ℤ)+k)).prod) =
      openFact current xs * fact (xs.getLastD current + first) *
        (upperInv current k * lowerInv first k * tailKernel xs k) := by
  induction xs generalizing current with
  | nil =>
    simp only [edgesFrom, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.getLastD_nil, openFact, one_mul, edge_factorization, tailKernel]
    ring
  | cons x xs ih =>
    simp only [edgesFrom, List.map_cons, List.prod_cons, map_mul, ih,
      edge_factorization, openFact, List.getLastD_cons, tailKernel, kernel]
    ring

theorem weight_factorization (x : ℕ) (xs : List ℕ) (k : ℕ) :
    embed (cyclicWeight (x::xs) k) =
      openFact x xs * fact (x+(x::xs).getLastD 0) * (kernel x k * tailKernel xs k) := by
  simp only [cyclicWeight, cyclicPairs, walk_factorization, List.getLastD_cons, kernel]
  rw [Nat.add_comm (xs.getLastD x) x]

theorem denominator_fraction {x : ℕ} {xs : List ℕ} {a : ℕ} (ha : a ≤ x)
    (hp : 0 < (x::xs).getLastD 0) :
    embed (denominator (x::xs) a) =
      fact (x+(x::xs).getLastD 0) / (fact (x-a) * fact ((x::xs).getLastD 0+a-1)) := by
  generalize hlast : (x::xs).getLastD 0 = y at hp ⊢
  unfold denominator last first
  rw [List.headD_cons, hlast, ← Int.ofNat_sub ha, map_mul,
    gauss_fraction (by omega : x-a ≤ x+y), show x+y-(x-a)=y+a by omega]
  rw [show fact (y+a) = fact (y+a-1) * embed (qi (y+a)) by
    simpa only [show (y+a-1)+1=y+a by omega] using fact_succ (y+a-1)]
  have hqi : embed (qi (y+a)) ≠ 0 :=
    (map_eq_zero_iff _ embed_injective).not.mpr (qi_ne_zero (by omega))
  field_simp [fact_ne_zero, hqi]

def baseWeight (j : ℤ) (r k : ℕ) : K :=
  embed (qi (2*k)) * embed (qi k)^(2*r) * mono (j*(k : ℤ)^2-((r : ℤ)+1)*k)

@[simp] theorem baseWeight_zero (j : ℤ) (r : ℕ) : baseWeight j r 0 = 0 := by simp [baseWeight]

theorem normalized_cycle {x : ℕ} {xs : List ℕ} {a : ℕ} (ha : a ≤ x)
    (hp : 0 < (x::xs).getLastD 0) (j : ℤ) (r : ℕ) :
    expression (x::xs) j a r =
      (fact (x-a) * fact ((x::xs).getLastD 0+a-1) * openFact x xs) *
        ∑ k ∈ Finset.Icc a x, baseWeight j r k * (kernel x k * tailKernel xs k) := by
  rw [expression_eq_div, denominator_fraction ha hp]
  unfold numerator
  simp only [map_sum, map_pow, map_mul, first, List.headD_cons, weight_factorization]
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold baseWeight mono
  field_simp [fact_ne_zero]

theorem kernel_chu (x y k : ℕ) :
    fact (x+y) * (kernel x k * kernel y k) =
      ∑ l ∈ Finset.Icc k (min x y),
        mono ((l : ℤ)^2-(k : ℤ)^2) * kernel l k / (fact (x-l) * fact (y-l)) := by
  by_cases h : k ≤ min x y
  · have hx : k ≤ x := (le_min_iff.mp h).1
    have hy : k ≤ y := (le_min_iff.mp h).2
    have hq := congrArg (fun p : ℤ[X] => embed (toLaurent p)) (qChu hx hy)
    have hgb (n : ℕ) (k : ℤ) : toLaurent (gauss n k) = gb n k := rfl
    simp only [map_sum, map_mul, toLaurent_X_pow, hgb] at hq
    apply mul_right_cancel₀ (mul_ne_zero (fact_ne_zero (x-k)) (fact_ne_zero (y+k)))
    calc
      _ = embed (gb (x+y) (↑(x+k) : ℤ)) := by
        rw [gauss_fraction (by omega : x+k ≤ x+y),
          show x+y-(x+k)=y-k by omega, kernel_inside hx, kernel_inside hy]
        field_simp [fact_ne_zero]
      _ = _ := by
        rw [hq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l hl => ?_
        simp only [Finset.mem_Icc, le_min_iff] at hl
        have he : (↑(l*l-k*k) : ℤ) = (l : ℤ)^2-(k : ℤ)^2 := by
          rw [Int.ofNat_sub (Nat.mul_le_mul hl.1 hl.1), Nat.cast_mul, Nat.cast_mul]
          ring
        rw [he, gauss_fraction (by omega : l-k ≤ x-k),
          gauss_fraction (by omega : l+k ≤ y+k), show x-k-(l-k)=x-l by omega,
          show y+k-(l+k)=y-l by omega, kernel_inside hl.1, mono]
        field_simp [fact_ne_zero]
  · rw [Finset.Icc_eq_empty h, Finset.sum_empty]
    by_cases hx : k ≤ x
    · have hy : y < k := by omega
      simp [kernel_outside hy]
    · simp [kernel_outside (Nat.lt_of_not_ge hx)]

end Catalan
```

## CatalanReduction.lean

```lean
import CatalanFactorials

open LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

def reductionIndices (a x y : ℕ) : Finset ℕ := Finset.Icc (max a 1) (min x y)

theorem reduction_bounds {a x y l : ℕ} (hl : l ∈ reductionIndices a x y) :
    a ≤ l ∧ 0 < l ∧ l ≤ x ∧ l ≤ y := by
  unfold reductionIndices at hl
  simp only [Finset.mem_Icc, max_le_iff, le_min_iff] at hl
  omega

private theorem reduce_term (x y a : ℕ) (xs : List ℕ) (j : ℤ) (r k : ℕ) (hak : a ≤ k) :
    fact (x+y) * (baseWeight j r k * (kernel x k * (kernel y k * tailKernel xs k))) =
      ∑ l ∈ reductionIndices a x y, (mono ((l : ℤ)^2) / (fact (x-l) * fact (y-l))) *
        (baseWeight (j-1) r k * (kernel l k * tailKernel xs k)) := by
  by_cases hk : k=0
  · subst k
    simp
  · have hc := kernel_chu x y k
    have hsub : Finset.Icc k (min x y) ⊆ reductionIndices a x y := by
      intro l hl
      simp only [reductionIndices, Finset.mem_Icc, max_le_iff] at hl ⊢
      omega
    rw [Finset.sum_subset hsub (fun l hl hn => by
      have hk' : l < k := by
        simp only [reductionIndices, Finset.mem_Icc, max_le_iff] at hl hn
        omega
      simp [kernel_outside hk'])] at hc
    calc
      _ = fact (x+y) * (kernel x k * kernel y k) * (baseWeight j r k * tailKernel xs k) := by ring
      _ = _ := by
        rw [hc, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [baseWeight, div_eq_mul_inv]
        have hphase :
            mono ((l : ℤ)^2-(k : ℤ)^2) * mono (j*(k : ℤ)^2-((r : ℤ)+1)*k) =
              mono ((l : ℤ)^2) * mono ((j-1)*(k : ℤ)^2-((r : ℤ)+1)*k) := by
          rw [mono_mul, mono_mul]
          congr 1
          ring
        calc
          _ = (mono ((l : ℤ)^2-(k : ℤ)^2) * mono (j*(k : ℤ)^2-((r : ℤ)+1)*k)) *
              ((fact (x-l) * fact (y-l))⁻¹ * kernel l k * tailKernel xs k *
                embed (qi (2*k)) * embed (qi k)^(2*r)) := by ring
          _ = _ := by rw [hphase]; ring

private theorem reduced_raw {x y a : ℕ} (xs : List ℕ) (j : ℤ) (r : ℕ) (ha : a ≤ x)
    (hp : 0 < (x::y::xs).getLastD 0) :
    expression (x::y::xs) j a r =
      (fact (x-a) * fact ((x::y::xs).getLastD 0+a-1) * openFact y xs) *
        ∑ l ∈ reductionIndices a x y, (mono ((l : ℤ)^2) / (fact (x-l) * fact (y-l))) *
          ∑ k ∈ Finset.Icc a l, baseWeight (j-1) r k * (kernel l k * tailKernel xs k) := by
  rw [normalized_cycle ha hp]
  simp only [openFact, tailKernel, List.map_cons, List.prod_cons]
  have hinner : ∀ k, (kernel y k * (List.map (fun n => kernel n k) xs).prod) =
      kernel y k * tailKernel xs k := fun _ => rfl
  simp only [hinner]
  calc
    _ = (fact (x-a) * fact ((x::y::xs).getLastD 0+a-1) * openFact y xs) *
        ∑ k ∈ Finset.Icc a x, fact (x+y) *
          (baseWeight j r k * (kernel x k * (kernel y k * tailKernel xs k))) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      calc
        _ = ∑ k ∈ Finset.Icc a x, ∑ l ∈ reductionIndices a x y,
            (mono ((l : ℤ)^2) / (fact (x-l) * fact (y-l))) *
              (baseWeight (j-1) r k * (kernel l k * tailKernel xs k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          exact reduce_term x y a xs j r k (Finset.mem_Icc.mp hk).1
        _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [← Finset.mul_sum]
          congr 1
          symm
          have hlx := (reduction_bounds hl).2.2.1
          apply Finset.sum_subset
          · intro k hk
            simp only [Finset.mem_Icc] at hk ⊢
            omega
          · intro k hk hkl
            have hk' : l < k := by simp only [Finset.mem_Icc] at hk hkl; omega
            simp [kernel_outside hk']

def coefficientTwo (x y a l : ℕ) : LR :=
  T ((l : ℤ)^2) * gb (x-a) (↑(l-a) : ℤ) * gb (y+a-1) (↑(l+a-1) : ℤ)

def coefficientMany (x y z a l : ℕ) : LR :=
  T ((l : ℤ)^2) * gb (x-a) (↑(l-a) : ℤ) * gb (y+z) (↑(y-l) : ℤ)

theorem cycle_reduce_two {x y a : ℕ} (hy : 0 < y) (ha : a ≤ x) (j : ℤ) (r : ℕ) :
    expression [x,y] j a r =
      ∑ l ∈ reductionIndices a x y, embed (coefficientTwo x y a l) *
        expression [l] (j-1) a r := by
  rw [reduced_raw [] j r ha (by simpa using hy), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨hal, hlpos, hlx, hly⟩ := reduction_bounds hl
  rw [normalized_cycle (xs := []) hal (by simpa using hlpos)]
  simp only [List.getLastD_cons, List.getLastD_nil, openFact, coefficientTwo, map_mul]
  rw [gauss_fraction (by omega : l-a ≤ x-a),
    gauss_fraction (by omega : l+a-1 ≤ y+a-1),
    show x-a-(l-a)=x-l by omega, show y+a-1-(l+a-1)=y-l by omega]
  unfold mono
  field_simp [fact_ne_zero]

theorem cycle_reduce_many {x y z a : ℕ} (xs : List ℕ) (hy : 0 < (z::xs).getLastD 0)
    (ha : a ≤ x) (j : ℤ) (r : ℕ) :
    expression (x::y::z::xs) j a r =
      ∑ l ∈ reductionIndices a x y, embed (coefficientMany x y z a l) *
        expression (l::z::xs) (j-1) a r := by
  have hp : 0 < (x::y::z::xs).getLastD 0 := by
    simpa only [List.getLastD_cons] using hy
  rw [reduced_raw (z::xs) j r ha hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨hal, _, hlx, hly⟩ := reduction_bounds hl
  rw [normalized_cycle (xs := z::xs) hal (by simpa only [List.getLastD_cons] using hy)]
  simp only [List.getLastD_cons, openFact, coefficientMany, map_mul]
  rw [gauss_fraction (by omega : l-a ≤ x-a),
    gauss_fraction (by omega : y-l ≤ y+z),
    show x-a-(l-a)=x-l by omega, show y+z-(y-l)=l+z by omega]
  unfold mono
  field_simp [fact_ne_zero]

theorem coefficientTwo_nonnegative (x y a l : ℕ) : Nonnegative (coefficientTwo x y a l) :=
  ((nonnegative_T _).mul (nonnegative_gb _ _)).mul (nonnegative_gb _ _)

theorem coefficientMany_nonnegative (x y z a l : ℕ) : Nonnegative (coefficientMany x y z a l) :=
  ((nonnegative_T _).mul (nonnegative_gb _ _)).mul (nonnegative_gb _ _)

#check cycle_reduce_two
#check cycle_reduce_many
#print axioms cycle_reduce_two
#print axioms cycle_reduce_many

end Catalan
```

## CatalanReflection.lean

```lean
import CatalanMoments

open Polynomial LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

theorem invert_qi (n : ℕ) : invert (qi n) = T (1-(n : ℤ)) * qi n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      invert (qi (n+1)) = T (1-(n : ℤ)) * qi n + T (-(n : ℤ)) := by
        rw [qi_add, qi_one, mul_one, map_add, ih, invert_T]
      _ = T (-(n : ℤ)) * (1 + T 1 * qi n) := by
        rw [show (T (1-(n : ℤ)) : LR) = T (-(n : ℤ)) * T 1 by
          rw [T_mul_T]; congr 1; omega]
        ring
      _ = _ := by
        rw [← qi_one_add, Nat.add_comm 1 n]
        congr 2
        omega

private theorem gr_symm (k l : ℕ) : gr k l = gr l k := congrArg toLaurent (rect_symm k l)

private theorem gr_pascal (k l : ℕ) :
    gr (k+1) (l+1) = gr (k+1) l + T (↑(l+1) : ℤ) * gr k (l+1) := by
  simpa [gr] using congrArg (toLaurent (R := ℤ)) (rect_succ_succ k l)

private theorem gr_pascal' (k l : ℕ) :
    gr (k+1) (l+1) = T (↑(k+1) : ℤ) * gr (k+1) l + gr k (l+1) := by
  rw [gr_symm (k+1) (l+1), gr_pascal l k, gr_symm (l+1) k, gr_symm l (k+1), add_comm]

theorem invert_gr (k l : ℕ) : invert (gr k l) = T (-(k : ℤ)*(l : ℤ)) * gr k l := by
  induction k generalizing l with
  | zero => simp [T_zero]
  | succ k hk =>
    induction l with
    | zero => simp [T_zero]
    | succ l hl =>
      calc
        invert (gr (k+1) (l+1)) =
            T (-(↑(k+1) : ℤ)*(l : ℤ)) * gr (k+1) l +
            (T (-(↑(l+1) : ℤ)) * T (-(k : ℤ)*(↑(l+1) : ℤ))) * gr k (l+1) := by
          rw [gr_pascal, map_add, map_mul, invert_T, hl, hk, mul_assoc]
        _ = T (-(↑(k+1) : ℤ)*(↑(l+1) : ℤ)) *
              (T (↑(k+1) : ℤ) * gr (k+1) l + gr k (l+1)) := by
          rw [mul_add, ← mul_assoc, T_mul_T, T_mul_T]
          have h₁ : -(↑(l+1) : ℤ)+(-(k : ℤ)*(↑(l+1) : ℤ)) =
              -(↑(k+1) : ℤ)*(↑(l+1) : ℤ) := by simp only [Nat.cast_add, Nat.cast_one]; ring
          have h₂ : -(↑(k+1) : ℤ)*(↑(l+1) : ℤ)+(↑(k+1) : ℤ) =
              -(↑(k+1) : ℤ)*(l : ℤ) := by simp only [Nat.cast_add, Nat.cast_one]; ring
          rw [h₁, h₂]
        _ = _ := by rw [← gr_pascal']

private theorem invert_gb_in {n k : ℕ} (h : k ≤ n) :
    invert (gb n (k : ℤ)) = T (-(k : ℤ) * ((n : ℤ)-k)) * gb n (k : ℤ) := by
  rw [gb_rect_of_add (l := n-k) (Nat.add_sub_of_le h).symm, invert_gr, Int.ofNat_sub h]

private theorem invert_edge (x y k : ℕ) :
    invert (gb (x+y) ((x : ℤ)+k)) =
      T ((k : ℤ)^2 - (x : ℤ)*y + ((x : ℤ)-y)*k) * gb (x+y) ((x : ℤ)+k) := by
  by_cases h : k ≤ y
  · rw [← Nat.cast_add, invert_gb_in (by omega : x+k ≤ x+y)]
    congr 2
    simp only [Nat.cast_add]
    ring
  · have hz : gb (x+y) ((x : ℤ)+k) = 0 := by
      unfold gb
      rw [gauss_outside (Or.inr (by omega)), map_zero]
    rw [hz, map_zero, mul_zero]

def cycleCost (ns : List ℕ) : ℤ :=
  ((cyclicPairs ns).map fun xy => (xy.1 : ℤ)*xy.2).sum

private theorem invert_walk (first current : ℕ) (xs : List ℕ) (k : ℕ) :
    invert (((edgesFrom first current xs).map fun xy => gb (xy.1+xy.2) ((xy.1 : ℤ)+k)).prod) =
      T (((xs.length : ℤ)+1)*(k : ℤ)^2 -
        ((edgesFrom first current xs).map fun xy => (xy.1 : ℤ)*xy.2).sum +
          ((current : ℤ)-first)*k) *
      ((edgesFrom first current xs).map fun xy => gb (xy.1+xy.2) ((xy.1 : ℤ)+k)).prod := by
  induction xs generalizing current with
  | nil => simp [edgesFrom, invert_edge]
  | cons next xs ih =>
    simp only [edgesFrom, List.map_cons, List.prod_cons, List.sum_cons, map_mul, invert_edge, ih,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    conv_lhs => rw [mul_mul_mul_comm, T_mul_T]
    congr 2
    ring

theorem invert_cyclicWeight (ns : List ℕ) (k : ℕ) :
    invert (cyclicWeight ns k) =
      T ((ns.length : ℤ)*(k : ℤ)^2-cycleCost ns) * cyclicWeight ns k := by
  cases ns with
  | nil => simp [cyclicWeight, cyclicPairs, cycleCost, T_zero]
  | cons n ns =>
    simpa [cyclicWeight, cyclicPairs, cycleCost] using invert_walk n n ns k

def numeratorShift (ns : List ℕ) (r : ℕ) : ℤ :=
  2*(r : ℤ)+1-cycleCost ns

theorem invert_numerator (ns : List ℕ) (j : ℤ) (a r : ℕ) :
    invert (numerator ns ((ns.length : ℤ)-j) a r) =
      T (numeratorShift ns r) * numerator ns j a r := by
  unfold numerator
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_mul, map_pow, invert_T, invert_qi, invert_cyclicWeight, mul_pow, T_pow, Nat.cast_mul]
  let g := qi (2*k) * qi k^(2*r) * cyclicWeight ns k
  calc
    _ = (T (1-(↑(2 : ℕ) : ℤ)*(k : ℤ)) *
        T ((↑(2 : ℕ) : ℤ)*(r : ℤ)*(1-(k : ℤ))) *
        T (-(((ns.length : ℤ)-j)*(k : ℤ)^2-((r : ℤ)+1)*k)) *
        T ((ns.length : ℤ)*(k : ℤ)^2-cycleCost ns)) * g := by
      unfold g
      ring
    _ = _ := by
      have he :
          1-(↑(2 : ℕ) : ℤ)*(k : ℤ) + (↑(2 : ℕ) : ℤ)*(r : ℤ)*(1-(k : ℤ)) +
              (-(((ns.length : ℤ)-j)*(k : ℤ)^2-((r : ℤ)+1)*k)) +
              ((ns.length : ℤ)*(k : ℤ)^2-cycleCost ns) =
            numeratorShift ns r + (j*(k : ℤ)^2-((r : ℤ)+1)*k) := by
        simp only [numeratorShift, Nat.cast_ofNat]
        ring
      rw [T_mul_T, T_mul_T, T_mul_T, he, T_add]
      unfold g
      ring

def denominatorShift (ns : List ℕ) (a : ℕ) : ℤ :=
  1-((last ns : ℤ)+a) - ((first ns : ℤ)-a)*((last ns : ℤ)+a)

theorem invert_denominator (ns : List ℕ) {a : ℕ} (ha : a ≤ first ns) :
    invert (denominator ns a) = T (denominatorShift ns a) * denominator ns a := by
  unfold denominator
  rw [← Int.ofNat_sub ha, map_mul, invert_qi, invert_gb_in (by omega : first ns-a ≤ first ns+last ns)]
  rw [mul_mul_mul_comm, T_mul_T]
  congr 2
  unfold denominatorShift
  rw [Int.ofNat_sub ha]
  simp only [Nat.cast_add]
  ring

theorem reflect_witness (ns : List ℕ) (j : ℤ) {a : ℕ} (r : ℕ) (ha : a ≤ first ns)
    (hD : denominator ns a ≠ 0) {L : LR}
    (h : expression ns ((ns.length : ℤ)-j) a r = embed L) (hL : Nonnegative L) :
    ∃ M : LR, expression ns j a r = embed M ∧ Nonnegative M := by
  refine ⟨T (denominatorShift ns a-numeratorShift ns r) * invert L, ?_,
    (nonnegative_T _).mul (nonnegative_invert hL)⟩
  rw [expression_eq_embed_iff _ _ _ _ hD] at h ⊢
  have hr := congrArg (invert (R := ℤ)) h
  simp only [map_mul, invert_numerator, invert_denominator ns ha] at hr
  calc
    _ = T (-(numeratorShift ns r)) * (T (numeratorShift ns r) * numerator ns j a r) := by
      simp only [← mul_assoc, T_mul_T, neg_add_cancel, T_zero, one_mul]
    _ = _ := by
      rw [hr, T_sub]
      ring

end Catalan
```

## CatalanConjecture.lean

```lean
import CatalanInterpolation
import CatalanReduction
import CatalanReflection

open LaurentPolynomial
open scoped BigOperators

noncomputable section

namespace Catalan

private def reductionCoefficient (x y a l : ℕ) : List ℕ → LR
  | [] => coefficientTwo x y a l
  | z::_ => coefficientMany x y z a l

private theorem reductionCoefficient_nonnegative (x y a l : ℕ) (xs : List ℕ) :
    Nonnegative (reductionCoefficient x y a l xs) := by
  cases xs with
  | nil => exact coefficientTwo_nonnegative x y a l
  | cons z _ => exact coefficientMany_nonnegative x y z a l

private theorem cycle_reduce {x y a : ℕ} (xs : List ℕ) (hy : 0 < y)
    (hp : ∀ n ∈ xs, 0 < n) (ha : a ≤ x) (j : ℤ) (r : ℕ) :
    expression (x::y::xs) j a r =
      ∑ l ∈ reductionIndices a x y, embed (reductionCoefficient x y a l xs) *
        expression (l::xs) (j-1) a r := by
  cases xs with
  | nil => exact cycle_reduce_two hy ha j r
  | cons z zs =>
    have hz : 0 < (z::zs).getLastD 0 := hp _ (by
      rw [List.getLastD_cons]
      exact List.getLastD_mem_cons)
    exact cycle_reduce_many zs hz ha j r

private theorem combine_witnesses (s : Finset ℕ) (c : ℕ → LR) (f : ℕ → K)
    (hc : ∀ l ∈ s, Nonnegative (c l)) (P : Prop)
    (hf : ∀ l ∈ s, ∃ L : LR, f l = embed L ∧ (P → Nonnegative L)) :
    ∃ L : LR, (∑ l ∈ s, embed (c l) * f l) = embed L ∧ (P → Nonnegative L) := by
  classical
  let F (l : ℕ) : LR := if h : l ∈ s then (hf l h).choose else 0
  have hF (l : ℕ) (hl : l ∈ s) : F l = (hf l hl).choose := dite_eq_left hl
  refine ⟨∑ l ∈ s, c l * F l, ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [map_mul, hF l hl]
    exact congrArg (fun t => embed (c l) * t) (hf l hl).choose_spec.1
  · intro h
    refine nonnegative_sum _ _ fun l hl => (hc l hl).mul ?_
    rw [hF l hl]
    exact (hf l hl).choose_spec.2 h

private theorem singleton_cases {n a : ℕ} (hn : 0 < n) (ha : a ≤ n) (j : ℤ) (r : ℕ) :
    ∃ L : LR, expression [n] j a r = embed L ∧
      (0 ≤ j → j ≤ ([n].length : ℤ) → Nonnegative L) := by
  by_cases h₀ : j=0
  · subst j
    obtain ⟨L, hL, hp⟩ := singleton_zero_phase hn ha r
    exact ⟨L, hL, fun _ _ => hp⟩
  · by_cases h₁ : j=1
    · subst j
      obtain ⟨L, hL, hp⟩ := singleton_zero_phase hn ha r
      have hD := denominator_ne_zero [n] (by simp) (by simpa using hn) ha
      obtain ⟨M, hM, hMp⟩ := reflect_witness [n] 1 r ha hD (by simpa using hL) hp
      exact ⟨M, hM, fun _ _ => hMp⟩
    · obtain ⟨L, hL⟩ := singleton_integral hn ha j r
      refine ⟨L, hL, ?_⟩
      intro hj hj'
      simp at hj'
      omega

private theorem cons_cases (xs : List ℕ) :
    ∀ x : ℕ, 0 < x → (∀ n ∈ xs, 0 < n) →
      ∀ (j : ℤ) (a r : ℕ), a ≤ x →
        ∃ L : LR, expression (x::xs) j a r = embed L ∧
          (0 ≤ j → j ≤ ((x::xs).length : ℤ) → Nonnegative L) := by
  induction xs with
  | nil =>
    intro x hx _ j a r ha
    exact singleton_cases hx ha j r
  | cons y xs ih =>
    intro x hx hp j a r ha
    have hy : 0 < y := hp _ (by simp)
    have hxs : ∀ n ∈ xs, 0 < n := fun n hn => hp n (List.mem_cons_of_mem _ hn)
    let m : ℤ := ((x::y::xs).length : ℤ)
    have hgen (u : ℤ) : ∃ L : LR, expression (x::y::xs) u a r = embed L ∧
        ((1 ≤ u ∧ u ≤ m) → Nonnegative L) := by
      rw [cycle_reduce xs hy hxs ha u r]
      apply combine_witnesses
      · exact fun l _ => reductionCoefficient_nonnegative x y a l xs
      · intro l hl
        obtain ⟨hal, hlpos, _, _⟩ := reduction_bounds hl
        obtain ⟨L, hL, hLp⟩ := ih l hlpos hxs (u-1) a r hal
        refine ⟨L, hL, fun hp => hLp (by omega) ?_⟩
        simp only [m, List.length_cons, Nat.cast_add, Nat.cast_one] at hp ⊢
        omega
    by_cases h : j=0
    · subst j
      obtain ⟨L,hL,hLp⟩ := hgen m
      have hm : 1 ≤ m := by simp [m]; omega
      have hD := denominator_ne_zero (x::y::xs) (by simp) (by
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact hx
        · exact hp _ hn) ha
      obtain ⟨M, hM, hMp⟩ := reflect_witness (x::y::xs) 0 r ha hD
        (by simpa only [sub_zero, m] using hL) (hLp ⟨hm, le_rfl⟩)
      exact ⟨M, hM, fun _ _ => hMp⟩
    · obtain ⟨L,hL,hLp⟩ := hgen j
      exact ⟨L, hL, fun hj hj' => hLp ⟨by omega, hj'⟩⟩

/-- Guo and Lian, Conjecture 6.1, with integer coefficients for every integer phase. -/
theorem mathdb381408 : GuoLianConjecture := by
  intro ns hne hp j a r ha
  cases ns with
  | nil => exact (hne rfl).elim
  | cons x xs =>
    exact cons_cases xs x (hp x (by simp))
      (fun n hn => hp n (List.mem_cons_of_mem _ hn)) j a r ha

theorem mathdb381408_laurent (ns : List ℕ) (hne : ns ≠ [])
    (hp : ∀ n ∈ ns, 0 < n) (j : ℤ) (a r : ℕ) (ha : a ≤ first ns) :
    ∃ L : LR, expression ns j a r = embed L := by
  obtain ⟨L, hL, _⟩ := mathdb381408 ns hne hp j a r ha
  exact ⟨L, hL⟩

theorem mathdb381408_nonnegative (ns : List ℕ) (hne : ns ≠ [])
    (hp : ∀ n ∈ ns, 0 < n) (j : ℤ) (a r : ℕ) (ha : a ≤ first ns)
    (hj : 0 ≤ j) (hj' : j ≤ (ns.length : ℤ)) :
    ∃ L : LR, expression ns j a r = embed L ∧ ∀ z : ℤ, 0 ≤ L.coeff z := by
  obtain ⟨L, hL, hLp⟩ := mathdb381408 ns hne hp j a r ha
  exact ⟨L, hL, hLp hj hj'⟩

#check mathdb381408
#check mathdb381408_laurent
#check mathdb381408_nonnegative
#print GuoLianConjecture
#print axioms mathdb381408
#print axioms mathdb381408_laurent
#print axioms mathdb381408_nonnegative

end Catalan
```

