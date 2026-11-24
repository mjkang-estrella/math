# Complete Lean source appendix

Modules are in import order. Extract each block byte for byte.

### `FranelGauss.lean`

```lean
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

open Polynomial
open scoped BigOperators

noncomputable section

namespace Franel

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

end Franel
```

### `FranelBasic.lean`

```lean
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace Franel

def franelPow (r k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℤ) ^ r

def signedSum (n r : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (r*k) * (3*(k : ℤ)+2) * franelPow r k

def halfSum (n r : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1),
    (-1 : ℤ)^(r*k) * (k+j+1 : ℕ) * (Nat.choose k j : ℤ)^r

@[simp] theorem franelPow_zero (k : ℕ) : franelPow 0 k = k+1 := by
  simp [franelPow]

 theorem reflected_weight (r k : ℕ) :
    2 * (∑ j ∈ Finset.range (k+1), (k+j+1 : ℕ) * (Nat.choose k j : ℤ)^r) =
      (3*(k : ℤ)+2) * franelPow r k := by
  have hreflect := Finset.sum_range_reflect
    (fun j => (k+j+1 : ℕ) * (Nat.choose k j : ℤ)^r) (k+1)
  have heq : (∑ j ∈ Finset.range (k+1), (k+j+1 : ℕ) * (Nat.choose k j : ℤ)^r) =
      ∑ j ∈ Finset.range (k+1), (2*(k : ℤ)-(j : ℤ)+1) * (Nat.choose k j : ℤ)^r := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := by simpa using Finset.mem_range.mp hj
    rw [show k+1-1-j=k-j by omega, Nat.choose_symm hjk]
    push_cast
    rw [Int.natCast_sub hjk]
    ring
  calc
    _ = (∑ j ∈ Finset.range (k+1), (k+j+1 : ℕ) * (Nat.choose k j : ℤ)^r) +
        ∑ j ∈ Finset.range (k+1), (2*(k : ℤ)-(j : ℤ)+1) * (Nat.choose k j : ℤ)^r := by
          rw [← heq]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, franelPow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring

 theorem twice_halfSum (n r : ℕ) : 2 * halfSum n r = signedSum n r := by
  unfold halfSum signedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [mul_assoc ((-1 : ℤ)^(r*k))]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm 2, mul_assoc, reflected_weight]

 theorem signedSum_zero (n : ℕ) : signedSum n 0 = (n : ℤ)^2 * (n+1) := by
  induction n with
  | zero => simp [signedSum]
  | succ n ih =>
    simp only [signedSum, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp only [Nat.zero_mul, pow_zero, one_mul, franelPow_zero, Nat.cast_add, Nat.cast_one]
    ring

 theorem guo_zero (n : ℕ) : (2*(n : ℤ)) ∣ signedSum n 0 := by
  rw [signedSum_zero]
  have heven : Even ((n : ℤ)*(n+1)) := by
    exact Int.even_mul_succ_self (n : ℤ)
  obtain ⟨a, ha⟩ := heven
  refine ⟨a, ?_⟩
  calc
    (n : ℤ)^2*(n+1) = n*((n : ℤ)*(n+1)) := by ring
    _ = (2*(n : ℤ))*a := by rw [ha]; ring

 theorem guo_one (r : ℕ) : (2 : ℤ) ∣ signedSum 1 r := by
  simp [signedSum, franelPow]

 theorem small_cases : ∀ n ∈ Finset.range 9, ∀ r ∈ Finset.range 7,
    1 ≤ n → (2*(n : ℤ)) ∣ signedSum n r := by decide

#print axioms twice_halfSum
#print axioms guo_zero
#print axioms guo_one
#print axioms small_cases
end Franel
```

### `FranelGenerating.lean`

```lean
import FranelGauss
import Mathlib.Data.Nat.Choose.Sum

open Polynomial
open scoped BigOperators

noncomputable section

namespace Franel

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

def tri : ℕ → ℕ
  | 0 => 0
  | k+1 => tri k + k

theorem tri_add (i j : ℕ) :
    tri (i+j) = tri i + tri j + i*j := by
  induction j with
  | zero => simp [tri]
  | succ j ih =>
    rw [Nat.add_succ, tri, tri, ih, Nat.mul_succ]
    omega

/-- The coefficient variable is the outer polynomial variable. -/
def gen (o n : ℕ) : ℤ[X][X] :=
  ∏ i ∈ Finset.range n, (1 + C ((X : ℤ[X])^(o+i)) * X)

theorem gen_coeff (o n k : ℕ) :
    (gen o n).coeff k = (X : ℤ[X])^(o*k+tri k) * gauss n (k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [gen, tri]
    | succ k =>
      rw [gauss_outside (n := 0) (k := (↑(k+1) : ℤ)) (by omega)]
      simp [gen, coeff_one]
  | succ n ih =>
    have hgen : gen o (n+1) = gen o n * (1 + C ((X : ℤ[X])^(o+n)) * X) := by
      simp [gen, Finset.prod_range_succ]
    rw [hgen, mul_add, mul_one, ← mul_assoc, coeff_add]
    cases k with
    | zero => simp [ih, tri]
    | succ k =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih, gauss_succ_succ, mul_add ((X : ℤ[X])^(o*(k+1)+tri (k+1))) _ _]
      by_cases hk : k ≤ n
      · have he : o*(k+1)+tri (k+1)+(n-k) =
            (o*k+tri k)+(o+n) := by
          rw [tri, Nat.mul_succ]
          omega
        congr 1
        calc
          (X : ℤ[X])^(o*k+tri k) * gauss n (k : ℤ) * X^(o+n)
              = X^((o*k+tri k)+(o+n)) * gauss n (k : ℤ) := by
                rw [pow_add]
                ring
          _ = _ := by rw [← he, pow_add, mul_assoc]
      · rw [gauss_outside (n := n) (k := (k : ℤ)) (by omega)]
        simp


theorem tri_double (k : ℕ) : 2 * tri k = k*(k-1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih =>
    rw [tri, Nat.mul_add, ih]
    cases k with
    | zero => simp
    | succ k => simp; ring

theorem gauss_eval_one (n k : ℕ) : (gauss n k).eval 1 = (Nat.choose n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k =>
      rw [gauss_outside (n := 0) (k := (↑(k+1) : ℤ)) (by omega)]
      simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [gauss_succ_succ]
      rw [eval_add, eval_mul, eval_pow, eval_X, one_pow, one_mul, ih (k+1), ih k]
      simp only [Nat.choose_succ_succ, Nat.cast_add]
      ring

#print axioms gauss_eval_one
#print axioms gen_coeff
end Franel
```

### `FranelPrime.lean`

```lean
import FranelBasic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open scoped BigOperators
namespace Franel

/-- Exchange the first and third coordinates of j+(k-j)+(n-1-k)=n-1. -/
theorem triangle_swap {A : Type*} [AddCommMonoid A] (n : ℕ) (f : ℕ → ℕ → A) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1), f k j) =
    ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1), f (n-1-j) (n-1-k) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨n-1-x.2, n-1-x.1⟩)
    (fun x _ => ⟨n-1-x.2, n-1-x.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    apply Sigma.ext
    · dsimp; omega
    · apply heq_of_eq; dsimp; omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    apply Sigma.ext
    · dsimp; omega
    · apply heq_of_eq; dsimp; omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    congr 1 <;> dsimp <;> omega

theorem choose_triangle_symm (m k j : ℕ) (hk : k ≤ m) (hj : j ≤ k) :
    m.choose k * k.choose j = m.choose (m-j) * (m-j).choose (m-k) := by
  rw [Nat.choose_mul hj, Nat.choose_symm (show j ≤ m by omega)]
  rw [← Nat.choose_symm (show m-k ≤ m-j by omega)]
  congr 2
  omega

theorem prime_top_choose (p k : ℕ) (hp : p.Prime) (hk : k < p) :
    ((p-1).choose k : ZMod p) = (-1 : ZMod p)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec := Nat.choose_succ_succ (p-1) k
    change (p-1+1).choose (k+1) = _ at hrec
    rw [Nat.sub_add_cancel hp.one_le] at hrec
    have hzero : (p.choose (k+1) : ZMod p) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr
        (hp.dvd_choose_self (by omega) hk)
    have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hrec
    push_cast at hcast
    rw [hzero, ih (by omega)] at hcast
    rw [pow_succ]
    linear_combination -hcast

/-- The integer multinomial kernel is unchanged under the coordinate exchange. -/
theorem prime_halfSum (p r : ℕ) (hp : p.Prime) : (p : ℤ) ∣ halfSum p r := by
  let M : ℕ → ℕ → ZMod p := fun k j =>
    (((p-1).choose k : ZMod p) * (k.choose j : ZMod p))^r
  have hm (k j : ℕ) (hk : k < p) (hj : j ≤ k) :
      M (p-1-j) (p-1-k) = M k j := by
    dsimp [M]
    congr 1
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod p))
      (choose_triangle_symm (p-1) k j (by omega) hj).symm
  have hswap := triangle_swap p (fun k j => M k j * (j : ZMod p))
  have hbalance : (∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (k+1),
      M k j * (j : ZMod p)) =
      ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (k+1), M k j * (p-1-k : ℕ) := by
    rw [hswap]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm k j (Finset.mem_range.mp hk) (by simpa using Finset.mem_range.mp hj)]
  have hv : ((halfSum p r : ℤ) : ZMod p) =
      ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (k+1),
        M k j * ((j : ZMod p) - (p-1-k : ℕ)) := by
    unfold halfSum
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j _
    have hk' : k < p := Finset.mem_range.mp hk
    have hweight : (k : ZMod p)+j+1 = (j : ZMod p) - (p-1-k : ℕ) := by
      have hnat : (p-1-k)+(k+j+1)=p+j := by omega
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hnat
      push_cast at h
      simp only [ZMod.natCast_self] at h
      linear_combination h
    dsimp [M]
    rw [prime_top_choose p k hp hk', mul_pow, ← pow_mul, show k*r=r*k by exact Nat.mul_comm _ _, hweight]
    ring
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [hv]
  simp_rw [mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr hbalance

theorem guo_prime (p r : ℕ) (hp : p.Prime) : (2*(p : ℤ)) ∣ signedSum p r := by
  rw [← twice_halfSum]
  exact mul_dvd_mul_left 2 (prime_halfSum p r hp)

#print axioms guo_prime
end Franel
```

### `FranelDeformation.lean`

```lean
import FranelBasic
import FranelGenerating
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.FieldSimp

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

def gval (z : ℂ) (n j : ℕ) : ℂ := (gauss n j).eval₂ (Int.castRingHom ℂ) z
def qval (z : ℂ) (n : ℕ) : ℂ := (qInt n).eval₂ (Int.castRingHom ℂ) z

def phase (z : ℂ) (n r k : ℕ) : ℂ :=
  (-1 : ℂ)^(r*k) * z^(n-1-k) / z^(r*tri (k+1))

def rootSum (z : ℂ) (n r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1),
    phase z n r k * gval z k j ^ r * qval z (k+j+1)

def deformation (n r : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (k+1),
    C ((-1 : ℤ)^(r*k)) * X^(n-1-k + r*(tri n-tri (k+1))) *
      gauss k j ^ r * qInt (k+j+1)

def qpoch (z : ℂ) (n : ℕ) : ℂ := ∏ i ∈ Finset.range n, (1-z^(i+1))
def multinomial (z : ℂ) (a b c : ℕ) : ℂ :=
  qpoch z (a+b+c) / (qpoch z a * qpoch z b * qpoch z c)

theorem qInt_eval_one (n : ℕ) : (qInt n).eval 1 = (n : ℤ) := by
  simp [qInt]

theorem deformation_eval_one (n r : ℕ) : (deformation n r).eval 1 = halfSum n r := by
  simp only [deformation, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    one_pow, mul_one, gauss_eval_one, qInt_eval_one, halfSum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tri_mono : Monotone tri := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_add_right _ _

theorem deformation_eval (z : ℂ) (hz : z ≠ 0) (n r : ℕ) :
    (deformation n r).eval₂ (Int.castRingHom ℂ) z = z^(r*tri n) * rootSum z n r := by
  simp only [deformation, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  unfold rootSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ht : tri (k+1) ≤ tri n := tri_mono (Finset.mem_range.mp hk)
  have he : n-1-k+r*(tri n-tri (k+1)) + r*tri (k+1) = r*tri n+(n-1-k) := by
    rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel ht, Nat.add_comm]
  have heval : z^(n-1-k+r*(tri n-tri (k+1))) =
      z^(r*tri n) * z^(n-1-k) / z^(r*tri (k+1)) := by
    apply (eq_div_iff (pow_ne_zero _ hz)).mpr
    rw [← pow_add, he, pow_add]
  change _ * _ * gval z k j ^ r * qval z (k+j+1) = _
  rw [heval]
  unfold phase
  simp only [map_pow, map_neg, map_one]
  ring

theorem qpoch_ne_zero (z : ℂ) (d n : ℕ) (_hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hn : n < d) : qpoch z n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  exact Ne.symm (hz.pow_ne_one_of_pos_of_lt (by omega) (by
    have := Finset.mem_range.mp hi
    omega))

theorem gval_pochhammer (z : ℂ) (n k : ℕ) (hk : k ≤ n) :
    gval z n k * (qpoch z k * qpoch z (n-k)) = qpoch z n := by
  have h := congrArg (fun P : ℤ[X] => P.eval₂ (Int.castRingHom ℂ) z) (gauss_pochhammer hk)
  simpa only [eval₂_mul, gval, pochhammer, eval₂_finsetProd, eval₂_sub, eval₂_one,
    eval₂_pow, eval₂_X, qpoch] using h

#print axioms deformation_eval_one
#print axioms deformation_eval
#print axioms qpoch_ne_zero
end Franel
```

### `FranelPhase.lean`

```lean
import FranelDeformation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.KummerExtension

open Polynomial
open scoped BigOperators
namespace Franel

theorem block_exponent (d N u s : ℕ) (hu : u < N) (hs : s < d) :
    N*d-1-(u*d+s) = (N-u-1)*d+(d-1-s) := by
  have hN : N = u+1+(N-u-1) := by omega
  conv_lhs => rw [hN]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Odd-order prototype of the phase bookkeeping in equation (13). -/
theorem phase_block_odd (z : ℂ) (d N u s r : ℕ) (_hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hodd : Odd d) (hu : u < N) (hs : s < d) :
    phase z (N*d) r (u*d+s) = (-1 : ℂ)^(r*u) * phase z d r s := by
  have ht : d ∣ tri (u*d) := by
    apply hodd.coprime_two_right.dvd_of_dvd_mul_left
    rw [tri_double]
    exact dvd_mul_of_dvd_left (dvd_mul_left d u) _
  have htri : z^tri (u*d+s+1) = z^tri (s+1) := by
    rw [show u*d+s+1 = u*d+(s+1) by omega, tri_add, pow_add, pow_add,
      (hz.pow_eq_one_iff_dvd _).mpr ht, one_mul,
      (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_of_dvd_left (dvd_mul_left d u) _), mul_one]
  have hsign : (-1 : ℂ)^(r*(u*d+s)) = (-1 : ℂ)^(r*u) * (-1 : ℂ)^(r*s) := by
    rw [Nat.mul_add, pow_add, show r*(u*d)=d*(r*u) by ring, pow_mul,
      hodd.neg_one_pow]
  have hexp : z^(N*d-1-(u*d+s)) = z^(d-1-s) := by
    rw [block_exponent d N u s hu hs, pow_add,
      (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_left d _), one_mul]
  unfold phase
  rw [hsign, hexp, show z^(r*tri (u*d+s+1)) = z^(r*tri (s+1)) by
    rw [Nat.mul_comm r, pow_mul, htri, ← pow_mul, Nat.mul_comm]]
  ring

theorem pow_tri_eq_prod (z : ℂ) (n : ℕ) : z^tri n = ∏ i ∈ Finset.range n, z^i := by
  induction n with
  | zero => simp [tri]
  | succ n ih => rw [tri, pow_add, Finset.prod_range_succ, ih]

/-- The constant coefficient of the product over all d-th roots retains both parity signs. -/
theorem root_tri_phase (z : ℂ) (d : ℕ) (hd : 2 ≤ d) (hz : IsPrimitiveRoot z d) :
    z^tri d = (-1 : ℂ)^(d+1) := by
  have h := congrArg (eval (0 : ℂ)) (X_pow_sub_C_eq_prod hz (by omega) (one_pow d : (1 : ℂ)^d=1))
  simp only [eval_sub, eval_pow, eval_X, zero_pow (by omega : d ≠ 0), eval_C,
    zero_sub, eval_prod, mul_one] at h
  have hp : (∏ i ∈ Finset.range d, -z^i) = (-1 : ℂ)^d * z^tri d := by
    calc
      _ = ∏ i ∈ Finset.range d, (-1 : ℂ)*z^i := by
        apply Finset.prod_congr rfl; intro i _; ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        ← pow_tri_eq_prod]
  rw [hp] at h
  apply mul_left_cancel₀ (pow_ne_zero d (by norm_num : (-1 : ℂ) ≠ 0))
  rw [← h, pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

theorem root_tri_block (z : ℂ) (d u : ℕ) (hd : 2 ≤ d) (hz : IsPrimitiveRoot z d) :
    z^tri (u*d) = ((-1 : ℂ)^(d+1))^u := by
  induction u with
  | zero => simp [tri]
  | succ u ih =>
    rw [Nat.succ_mul, tri_add, pow_add, pow_add, ih, root_tri_phase z d hd hz,
      (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_of_dvd_left (dvd_mul_left d u) _), mul_one,
      pow_succ _ u]

theorem phase_block (z : ℂ) (d N u s r : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hu : u < N) (hs : s < d) :
    phase z (N*d) r (u*d+s) = (-1 : ℂ)^(r*u) * phase z d r s := by
  have htri : z^tri (u*d+s+1) =
      (-1 : ℂ)^((d+1)*u) * z^tri (s+1) := by
    rw [show u*d+s+1=u*d+(s+1) by omega, tri_add, pow_add, pow_add,
      root_tri_block z d u hd hz, ← pow_mul,
      (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_of_dvd_left (dvd_mul_left d u) _), mul_one]
  have hexp : z^(N*d-1-(u*d+s)) = z^(d-1-s) := by
    rw [block_exponent d N u s hu hs, pow_add,
      (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_left d _), one_mul]
  have hden : z^(r*tri (u*d+s+1)) =
      ((-1 : ℂ)^(r*(u*d)) * (-1 : ℂ)^(r*u)) * z^(r*tri (s+1)) := by
    rw [Nat.mul_comm r, pow_mul, htri, mul_pow, ← pow_mul,
      show (d+1)*u*r=r*(u*d)+r*u by ring, pow_add, ← pow_mul, Nat.mul_comm _ r]
  have hsq : (-1 : ℂ)^(r*u) * (-1 : ℂ)^(r*u) = 1 := by
    rw [← mul_pow]; simp
  have hnon : z ≠ 0 := hz.ne_zero (by omega)
  unfold phase
  rw [hexp, hden, Nat.mul_add, pow_add]
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ hnon))).mpr
  rw [show ((-1 : ℂ)^(r*u) * ((-1)^ (r*s) * z^(d-1-s) / z^(r*tri (s+1)))) *
      (((-1)^(r*(u*d)) * (-1)^(r*u)) * z^(r*tri (s+1))) =
      (-1)^(r*u) * ((-1)^(r*s) * z^(d-1-s)) *
      ((-1)^(r*(u*d)) * (-1)^(r*u)) by field_simp]
  calc
    _ = (-1 : ℂ)^(r*(u*d)) * (-1 : ℂ)^(r*s) * z^(d-1-s) *
        ((-1 : ℂ)^(r*u) * (-1 : ℂ)^(r*u)) := by rw [hsq, mul_one]
    _ = _ := by ring

#print axioms phase_block
#print axioms phase_block_odd
end Franel
```

### `FranelRoots.lean`

```lean
import FranelPhase
import FranelPrime

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

def cgen (z : ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ Finset.range n, (1+C (z^i)*X)

theorem cgen_coeff (z : ℂ) (n k : ℕ) :
    (cgen z n).coeff k = z^tri k * gval z n k := by
  have hm : cgen z n = (gen 0 n).map (eval₂RingHom (Int.castRingHom ℂ) z) := by
    simp [cgen, gen, Polynomial.map_prod]
  rw [hm, coeff_map, gen_coeff]
  simp [gval]

theorem cgen_succ (z : ℂ) (n : ℕ) :
    cgen z (n+1) = cgen z n * (1+C (z^n)*X) := by
  simp [cgen, Finset.prod_range_succ]

theorem cgen_full (z : ℂ) (d : ℕ) (hd : 2 ≤ d) (hz : IsPrimitiveRoot z d) :
    cgen z d = 1-C ((-1 : ℂ)^d)*X^d := by
  have hnon : z ≠ 0 := hz.ne_zero (by omega)
  have hprod := X_pow_sub_C_eq_prod hz.inv (by omega) (rfl : (-1 : ℂ)^d=(-1)^d)
  have hf (i : ℕ) : (1+C (z^i)*X : ℂ[X]) =
      C (z^i) * (X-C ((z⁻¹)^i * (-1))) := by
    have hp : z^i * (z⁻¹)^i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hnon, one_pow]
    rw [mul_sub, ← C_mul]
    have hc : z^i * ((z⁻¹)^i * (-1)) = -1 := by rw [← mul_assoc, hp, one_mul]
    rw [hc, C_neg, C_1]
    ring
  unfold cgen
  simp_rw [hf, Finset.prod_mul_distrib]
  rw [← map_prod, ← pow_tri_eq_prod, root_tri_phase z d hd hz, ← hprod]
  have hs : (-1 : ℂ)^(d+1) * (-1)^d = -1 := by
    rw [pow_succ, mul_right_comm, ← mul_pow]
    norm_num
  calc
    _ = C ((-1 : ℂ)^(d+1))*X^d - C (-1 : ℂ) := by rw [mul_sub, ← C_mul, hs]
    _ = _ := by rw [pow_succ, C_mul, C_neg, C_1]; ring

/-- Top Gaussian row, proved through coefficients without evaluating any singular quotient. -/
theorem gval_top (z : ℂ) (d k : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hk : k < d) :
    gval z (d-1) k = (-1 : ℂ)^k / z^(tri (k+1)) := by
  have hnon : z ≠ 0 := hz.ne_zero (by omega)
  have hcoeff : ∀ k < d, (cgen z (d-1)).coeff k * z^k = (-1 : ℂ)^k := by
    intro k hk
    induction k with
    | zero => simp [cgen_coeff, gval, gauss_zero_col, tri]
    | succ k ih =>
      have hrec := congrArg (fun P : ℂ[X] => P.coeff (k+1)) (cgen_succ z (d-1))
      rw [Nat.sub_add_cancel (by omega : 1 ≤ d), cgen_full z d hd hz] at hrec
      have hc0 : (1-C ((-1 : ℂ)^d)*X^d : ℂ[X]).coeff (k+1) = 0 := by
        rw [coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow]
        simp [show k+1 ≠ d by omega]
      rw [hc0, mul_add, mul_one, ← mul_assoc, coeff_add, coeff_mul_X, coeff_mul_C] at hrec
      have hp : z^(d-1) * z = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d), hz.pow_eq_one]
      calc
        _ = ((cgen z (d-1)).coeff (k+1) * z^k) * z := by rw [pow_succ]; ring
        _ = -((cgen z (d-1)).coeff k * z^k) := by
          have hr := congrArg (fun a : ℂ => a * z^(k+1)) hrec
          rw [pow_succ] at hr
          linear_combination -hr - ((cgen z (d-1)).coeff k * z^k) * hp
        _ = _ := by rw [ih (by omega), pow_succ]; ring
  have h := hcoeff k hk
  rw [cgen_coeff] at h
  apply (eq_div_iff (pow_ne_zero _ hnon)).mpr
  rw [tri, pow_add]
  calc
    _ = (z^tri k * gval z (d-1) k) * z^k := by ring
    _ = _ := h

#print axioms cgen_full
#print axioms gval_top
end Franel
```

### `FranelCancellation.lean`

```lean
import FranelRoots

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

theorem gval_quotient (z : ℂ) (d n k : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hn : n < d) (hk : k ≤ n) :
    gval z n k = qpoch z n / (qpoch z k * qpoch z (n-k)) := by
  apply (eq_div_iff (mul_ne_zero (qpoch_ne_zero z d k hd hz (by omega))
    (qpoch_ne_zero z d (n-k) hd hz (by omega)))).mpr
  exact gval_pochhammer z n k hk

theorem gval_kernel (z : ℂ) (d m k j : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hm : m < d) (hk : k ≤ m) (hj : j ≤ k) :
    gval z m k * gval z k j =
      qpoch z m / (qpoch z j * qpoch z (k-j) * qpoch z (m-k)) := by
  rw [gval_quotient z d m k hd hz hm hk, gval_quotient z d k j hd hz (by omega) hj]
  have hn := qpoch_ne_zero z d k hd hz (by omega)
  field_simp

theorem gval_kernel_symm (z : ℂ) (d m k j : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hm : m < d) (hk : k ≤ m) (hj : j ≤ k) :
    gval z m (m-j) * gval z (m-j) (m-k) = gval z m k * gval z k j := by
  rw [gval_kernel z d m k j hd hz hm hk hj,
    gval_kernel z d m (m-j) (m-k) hd hz hm (by omega) (by omega),
    show m-j-(m-k)=k-j by omega, show m-(m-j)=j by omega]
  ring

theorem qval_mul (z : ℂ) (n : ℕ) : qval z n * (1-z) = 1-z^n := by
  have h := congrArg (fun P : ℤ[X] => P.eval₂ (Int.castRingHom ℂ) z) (qInt_mul_one_sub n)
  simpa only [eval₂_mul, eval₂_sub, eval₂_one, eval₂_X, eval₂_pow, qval] using h

theorem primitive_weight (z : ℂ) (d k j : ℕ) (hz : z^d=1) (hk : k < d) :
    z^(d-1-k) * qval z (k+j+1) * (1-z) = z^(d-1-k)-z^j := by
  calc
    _ = z^(d-1-k) * (1-z^(k+j+1)) := by rw [mul_assoc, qval_mul]
    _ = z^(d-1-k) - z^(d-1-k+(k+j+1)) := by rw [pow_add]; ring
    _ = _ := by rw [show d-1-k+(k+j+1)=d+j by omega, pow_add, hz, one_mul]

theorem primitive_phase (z : ℂ) (d r k : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hk : k < d) :
    phase z d r k = z^(d-1-k) * gval z (d-1) k ^r := by
  rw [gval_top z d k hd hz hk, div_pow, ← pow_mul, Nat.mul_comm k r]
  unfold phase
  rw [Nat.mul_comm r (tri (k+1)), pow_mul]
  ring

/-- Primitive-order cancellation; unlike the block step, this includes r=0. -/
theorem primitive_vanish (z : ℂ) (d r : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) : rootSum z d r = 0 := by
  let M : ℕ → ℕ → ℂ := fun k j => (gval z (d-1) k * gval z k j)^r
  have hm (k j : ℕ) (hk : k < d) (hj : j ≤ k) :
      M (d-1-j) (d-1-k) = M k j := by
    dsimp [M]
    rw [gval_kernel_symm z d (d-1) k j hd hz (by omega) (by omega) hj]
  have hb : (∑ k ∈ Finset.range d, ∑ j ∈ Finset.range (k+1), M k j * z^j) =
      ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range (k+1), M k j * z^(d-1-k) := by
    rw [triangle_swap d (fun k j => M k j * z^j)]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm k j (Finset.mem_range.mp hk) (by simpa using Finset.mem_range.mp hj)]
  have hzero : rootSum z d r * (1-z) = 0 := by
    unfold rootSum
    simp_rw [Finset.sum_mul]
    calc
      _ = ∑ k ∈ Finset.range d, ∑ j ∈ Finset.range (k+1),
          M k j * (z^(d-1-k)-z^j) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro j _
        rw [primitive_phase z d r k hd hz (Finset.mem_range.mp hk)]
        dsimp [M]
        rw [mul_pow]
        calc
          _ = (gval z (d-1) k ^r * gval z k j ^r) *
              (z^(d-1-k) * qval z (k+j+1) * (1-z)) := by ring
          _ = _ := by rw [primitive_weight z d k j hz.pow_eq_one (Finset.mem_range.mp hk)]
      _ = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr hb.symm
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr (Ne.symm (hz.ne_one (by omega))))

#print axioms primitive_vanish
end Franel
```

### `FranelLucas.lean`

```lean
import FranelRoots
import Mathlib.Algebra.Polynomial.Expand

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

theorem cgen_add_period (z : ℂ) (a b : ℕ) (ha : z^a=1) :
    cgen z (a+b) = cgen z a * cgen z b := by
  simp only [cgen, Finset.prod_range_add, pow_add, ha, one_mul]

theorem cgen_block (z : ℂ) (d u s : ℕ) (hz : IsPrimitiveRoot z d) :
    cgen z (u*d+s) = cgen z d ^u * cgen z s := by
  induction u generalizing s with
  | zero => simp [cgen]
  | succ u ih =>
    rw [Nat.succ_mul, Nat.add_assoc, cgen_add_period z (u*d) (d+s)
      ((hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_left d u)),
      cgen_add_period z d s hz.pow_eq_one]
    have hu : cgen z (u*d) = cgen z d ^u := by
      simpa only [Nat.add_zero, show cgen z 0=1 by simp [cgen], mul_one] using ih 0
    rw [hu, pow_succ]
    ring

theorem binomial_coeff (a : ℂ) (u v : ℕ) :
    ((1+C a*X : ℂ[X])^u).coeff v = (Nat.choose u v : ℂ)*a^v := by
  induction u generalizing v with
  | zero => cases v <;> simp [coeff_one]
  | succ u ih =>
    rw [pow_succ, mul_add, mul_one, ← mul_assoc, coeff_add]
    cases v with
    | zero => simp [ih]
    | succ v =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih, Nat.choose_succ_succ]
      push_cast
      rw [pow_succ]
      ring

theorem lucas_coeff (z : ℂ) (d u v s t : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hs : s < d) (ht : t < d) :
    (cgen z (u*d+s)).coeff (v*d+t) =
      (Nat.choose u v : ℂ) * ((-1 : ℂ)^(d+1))^v * (cgen z s).coeff t := by
  let F : ℂ[X] := (1+C ((-1 : ℂ)^(d+1))*X)^u
  have hf : (cgen z d)^u = expand ℂ d F := by
    simp only [F, map_pow, map_add, map_one, map_mul, expand_C, expand_X]
    rw [cgen_full z d hd hz]
    congr 1
    simp only [pow_succ, C_neg, C_1, C_pow]
    ring
  rw [cgen_block z d u s hz, hf, coeff_mul]
  rw [Finset.sum_eq_single (v*d,t)]
  · rw [coeff_expand_mul (by omega), binomial_coeff]
  · intro p hp hne
    have hsum := Finset.mem_antidiagonal.mp hp
    by_cases hsmall : p.2 ≤ s
    · have hnd : ¬ d ∣ p.1 := by
        intro hdiv
        have hmod := congrArg (fun a => a % d) hsum
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt (show p.2 < d by omega), Nat.mul_comm v d, Nat.mul_add_mod,
          Nat.mod_eq_of_lt ht] at hmod
        have heq : p = (v*d,t) := by
          apply Prod.ext
          · dsimp; omega
          · exact hmod
        exact hne heq
      rw [coeff_expand (by omega), ite_eq_right hnd, zero_mul]
    · rw [cgen_coeff]
      have hg : gval z s p.2 = 0 := by
        unfold gval
        rw [gauss_outside (n := s) (k := (p.2 : ℤ)) (by omega), eval₂_zero]
      rw [hg, mul_zero, mul_zero]
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr rfl)).elim

theorem qLucas (z : ℂ) (d u v s t : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hs : s < d) (ht : t < d) :
    gval z (u*d+s) (v*d+t) = (Nat.choose u v : ℂ) * gval z s t := by
  have h := lucas_coeff z d u v s t hd hz hs ht
  rw [cgen_coeff, cgen_coeff] at h
  have hphase : z^tri (v*d+t) = ((-1 : ℂ)^(d+1))^v * z^tri t := by
    rw [tri_add, pow_add, pow_add, root_tri_block z d v hd hz,
      (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_of_dvd_left (dvd_mul_left d v) _), mul_one]
  rw [hphase] at h
  apply mul_left_cancel₀ (show ((-1 : ℂ)^(d+1))^v * z^tri t ≠ 0 from
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ (hz.ne_zero (by omega))))
  calc
    _ = (Nat.choose u v : ℂ) * ((-1 : ℂ)^(d+1))^v * (z^tri t * gval z s t) := h
    _ = _ := by ring

#print axioms qLucas
end Franel
```

### `FranelBlocks.lean`

```lean
import FranelLucas
import FranelCancellation

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

theorem sum_blocks {A : Type*} [AddCommMonoid A] (N d : ℕ) (f : ℕ → A) :
    (∑ k ∈ Finset.range (N*d), f k) =
      ∑ u ∈ Finset.range N, ∑ s ∈ Finset.range d, f (u*d+s) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem extend_gauss_sum (z : ℂ) (n k r : ℕ) (hr : 1 ≤ r) (hk : k < n) (w : ℕ → ℂ) :
    (∑ j ∈ Finset.range (k+1), gval z k j ^r * w j) =
      ∑ j ∈ Finset.range n, gval z k j ^r * w j := by
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  have hkj : k < j := by
    simp only [Finset.mem_range] at hj
    omega
  unfold gval
  rw [gauss_outside (n := k) (k := (j : ℤ)) (by omega), eval₂_zero,
    zero_pow (by omega : r ≠ 0), zero_mul]

theorem rootSum_rect (z : ℂ) (n r : ℕ) (hr : 1 ≤ r) :
    rootSum z n r = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range n,
      phase z n r k * gval z k j ^r * qval z (k+j+1) := by
  unfold rootSum
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [show ∀ j, phase z n r k * gval z k j ^r * qval z (k+j+1) =
      phase z n r k * (gval z k j ^r * qval z (k+j+1)) from fun j => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [extend_gauss_sum z n k r hr (Finset.mem_range.mp hk)]

theorem qval_block (z : ℂ) (d u v s t : ℕ) (hd : 2 ≤ d) (hz : IsPrimitiveRoot z d) :
    qval z (u*d+s+(v*d+t)+1) = qval z (s+t+1) := by
  apply mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm (hz.ne_one (by omega))))
  rw [qval_mul, qval_mul, show u*d+s+(v*d+t)+1=(u+v)*d+(s+t+1) by ring,
    pow_add, (hz.pow_eq_one_iff_dvd _).mpr (dvd_mul_left d _), one_mul]

theorem choose_sum_extend (N u r : ℕ) (hu : u < N) (hr : 1 ≤ r) :
    (∑ v ∈ Finset.range N, (Nat.choose u v : ℂ)^r) = (franelPow r u : ℂ) := by
  rw [franelPow]
  push_cast
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  rw [Nat.choose_eq_zero_of_lt (by
      simp only [Finset.mem_range] at hj
      omega),
    Nat.cast_zero, zero_pow (by omega : r ≠ 0)]

theorem four_sums (N d : ℕ) (A B : ℕ → ℕ → ℂ) :
    (∑ u ∈ Finset.range N, ∑ s ∈ Finset.range d,
      ∑ v ∈ Finset.range N, ∑ t ∈ Finset.range d, A u v * B s t) =
    (∑ u ∈ Finset.range N, ∑ v ∈ Finset.range N, A u v) *
      (∑ s ∈ Finset.range d, ∑ t ∈ Finset.range d, B s t) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]

theorem rootSum_block (z : ℂ) (d N r : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hr : 1 ≤ r) :
    rootSum z (N*d) r =
      (∑ u ∈ Finset.range N, (-1 : ℂ)^(r*u) * (franelPow r u : ℂ)) * rootSum z d r := by
  rw [rootSum_rect z (N*d) r hr, rootSum_rect z d r hr, sum_blocks]
  simp_rw [sum_blocks N d]
  calc
    _ = ∑ u ∈ Finset.range N, ∑ s ∈ Finset.range d,
        ∑ v ∈ Finset.range N, ∑ t ∈ Finset.range d,
        ((-1 : ℂ)^(r*u) * (Nat.choose u v : ℂ)^r) *
          (phase z d r s * gval z s t ^r * qval z (s+t+1)) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro t ht
      rw [phase_block z d N u s r hd hz (Finset.mem_range.mp hu) (Finset.mem_range.mp hs),
        qLucas z d u v s t hd hz (Finset.mem_range.mp hs) (Finset.mem_range.mp ht),
        qval_block z d u v s t hd hz, mul_pow]
      ring
    _ = _ := by
      rw [four_sums]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum, choose_sum_extend N u r (Finset.mem_range.mp hu) hr]

#print axioms rootSum_block
end Franel
```

### `FranelEndgame.lean`

```lean
import FranelDeformation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

/-- Integral monic descent: vanishing at every nontrivial n-th root suffices.
This is a general algebra lemma, with its root hypothesis explicitly visible. -/
theorem qInt_dvd_of_vanish (n : ℕ) (hn : 1 ≤ n) (P : ℤ[X])
    (h : ∀ z : ℂ, z^n = 1 → z ≠ 1 → P.eval₂ (Int.castRingHom ℂ) z = 0) :
    qInt n ∣ P := by
  let ι := Int.castRingHom ℂ
  have hmonic := qInt_monic (by omega : n ≠ 0)
  have hmul : (qInt n).map ι * (X-1) = (X^n-1 : ℂ[X]) := by
    simpa [qInt, Polynomial.map_sum, ι] using geom_sum_mul (X : ℂ[X]) n
  have hsep : Separable ((qInt n).map ι) := by
    apply (separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast (show n ≠ 0 by omega)) one_ne_zero).of_dvd
    exact ⟨X-1, hmul.symm⟩
  apply (map_dvd_map ι Int.cast_injective hmonic).mp
  by_cases hp0 : P.map ι = 0
  · simp [hp0]
  rw [IsAlgClosed.dvd_iff_roots_le_roots (hmonic.map ι).ne_zero hp0,
    Multiset.le_iff_count]
  intro z
  simp only [count_roots]
  by_cases hz : IsRoot ((qInt n).map ι) z
  · have hzn : z^n=1 := by
      have he := congrArg (eval z) hmul
      simp only [eval_mul, show ((qInt n).map ι).eval z = 0 from hz, zero_mul, eval_sub, eval_pow, eval_X, eval_one] at he
      exact sub_eq_zero.mp he.symm
    have hzone : z ≠ 1 := by
      intro he
      subst z
      have hv : ((qInt n).map ι).eval 1 = (n : ℂ) := by
        simp [qInt, ι]
      rw [show ((qInt n).map ι).eval 1 = 0 from hz] at hv
      have : n = 0 := by exact_mod_cast hv.symm
      omega
    have hpz : IsRoot (P.map ι) z := by
      simpa only [IsRoot, eval_map] using h z hzn hzone
    exact (rootMultiplicity_le_one_of_separable hsep z).trans
      (Nat.one_le_iff_ne_zero.mpr ((rootMultiplicity_pos hp0).mpr hpz).ne')
  · rw [rootMultiplicity_eq_zero hz]
    exact Nat.zero_le _

/-- Specialization preserves the integer divisor, rather than merely a rational quotient. -/
theorem halfSum_dvd_of_polynomial (n r : ℕ) (h : qInt n ∣ deformation n r) :
    (n : ℤ) ∣ halfSum n r := by
  have hval := map_dvd (evalRingHom (1 : ℤ)) h
  change (qInt n).eval 1 ∣ (deformation n r).eval 1 at hval
  simpa only [qInt_eval_one, deformation_eval_one] using hval

/-- Conditional assembly only: this is not the unconditional conjecture endpoint. -/
theorem guo_of_polynomial (n r : ℕ) (h : qInt n ∣ deformation n r) :
    (2*(n : ℤ)) ∣ signedSum n r := by
  rw [← twice_halfSum]
  exact mul_dvd_mul_left 2 (halfSum_dvd_of_polynomial n r h)

#print axioms qInt_dvd_of_vanish
#print axioms halfSum_dvd_of_polynomial
#print axioms guo_of_polynomial
end Franel
```

### `FranelConjecture.lean`

```lean
import FranelBlocks
import FranelEndgame

open Polynomial
open scoped BigOperators
noncomputable section
namespace Franel

theorem deformation_vanish (z : ℂ) (d n r : ℕ) (hd : 2 ≤ d)
    (hz : IsPrimitiveRoot z d) (hdn : d ∣ n) (hr : 1 ≤ r) :
    (deformation n r).eval₂ (Int.castRingHom ℂ) z = 0 := by
  obtain ⟨N, rfl⟩ := hdn
  rw [Nat.mul_comm d N, deformation_eval z (hz.ne_zero (by omega)),
    rootSum_block z d N r hd hz hr, primitive_vanish z d r hd hz, mul_zero, mul_zero]

theorem qInt_dvd_deformation (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    qInt n ∣ deformation n r := by
  apply qInt_dvd_of_vanish n hn
  intro z hzn hzone
  have hdn : orderOf z ∣ n := orderOf_dvd_of_pow_eq_one hzn
  have hp : 0 < orderOf z := Nat.pos_of_dvd_of_pos hdn hn
  have hone : orderOf z ≠ 1 := fun he => hzone (orderOf_eq_one_iff.mp he)
  exact deformation_vanish z (orderOf z) n r (by omega) (IsPrimitiveRoot.orderOf z) hdn hr

/-- Each cyclotomic factor also divides the deformation over the integers. -/
theorem cyclotomic_dvd_deformation (d n r : ℕ) (hd : 2 ≤ d)
    (hdn : d ∣ n) (hr : 1 ≤ r) : cyclotomic d ℤ ∣ deformation n r := by
  by_cases hn : n=0
  · simp [hn, deformation]
  have hfactor : cyclotomic d ℤ ∣ qInt n := by
    rw [qInt, ← prod_cyclotomic_eq_geom_sum (Nat.pos_of_ne_zero hn) ℤ]
    apply Finset.dvd_prod_of_mem
    exact Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors.mpr ⟨hdn, hn⟩⟩
  exact hfactor.trans (qInt_dvd_deformation n r (by omega) hr)

theorem halfSum_dvd (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (n : ℤ) ∣ halfSum n r :=
  halfSum_dvd_of_polynomial n r (qInt_dvd_deformation n r hn hr)

/-- Guo, arXiv:1201.0617, Conjecture 4.1 (4.6), all n ≥ 1 and r ≥ 0. -/
theorem guo_conj_4_1 (n r : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℤ)) ∣ ∑ k ∈ Finset.range n,
      (-1 : ℤ) ^ (r * k) * (3 * (k : ℤ) + 2) * franelPow r k := by
  change (2*(n : ℤ)) ∣ signedSum n r
  by_cases hr : r=0
  · subst r
    exact guo_zero n
  · exact guo_of_polynomial n r (qInt_dvd_deformation n r hn (by omega))

#check guo_conj_4_1
#print axioms guo_conj_4_1
#print axioms qInt_dvd_deformation
#print axioms cyclotomic_dvd_deformation
end Franel
```

### `FranelAudit.lean`

```lean
import FranelConjecture

open scoped BigOperators
#eval Lean.versionString
#check Franel.franelPow
#check Franel.guo_conj_4_1
#check Franel.guo_prime
#check Franel.guo_zero
#check Franel.guo_one
#check Franel.small_cases
#print axioms Franel.franelPow
#print axioms Franel.gauss_pochhammer
#print axioms Franel.gauss_eval_one
#print axioms Franel.gen_coeff
#print axioms Franel.guo_conj_4_1
#print axioms Franel.guo_prime
#print axioms Franel.guo_zero
#print axioms Franel.guo_one
#print axioms Franel.small_cases
#print axioms Franel.qLucas
#print axioms Franel.primitive_vanish
#print axioms Franel.phase_block
#print axioms Franel.rootSum_block
#print axioms Franel.qInt_dvd_deformation
#print axioms Franel.cyclotomic_dvd_deformation
```

