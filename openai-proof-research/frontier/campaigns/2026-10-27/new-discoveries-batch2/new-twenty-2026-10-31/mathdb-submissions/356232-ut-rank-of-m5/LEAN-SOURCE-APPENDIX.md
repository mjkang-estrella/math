# Lean source appendix (MathDB 356232)

Modules are listed in import order; each block is byte-identical to `src/<Module>.lean`.

### `M5Defs.lean`

```lean
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Subsemigroup.Defs

/-!
# Definitions for MathDB 356232 (Nyberg-Brodda, arXiv:2209.12612, Conjecture 2.11)

* `Zbar` is the max-plus semiring `ℤ ∪ {−∞}` (addition `max`, multiplication `+`).
  It is Mathlib's `MinTropical (WithTop ℤᵒᵈ)`: the minimum for the reversed order on `ℤ`
  is the maximum, and the adjoined top element `⊤` of `WithTop ℤᵒᵈ` is `−∞`.
  The sanity lemmas below (`zb_add_zb`, `zb_mul_zb`, `zero_eq_negInf`, `one_eq_zb_zero`,
  `cases_zb`, ...) check that this is literally max-plus over `ℤ ∪ {−∞}`.
* `UT n` is the subsemigroup of upper-triangular `n × n` matrices over `Zbar`
  (entries below the diagonal are `−∞`, which is the semiring zero).
* `M5` is the monoid presented by `⟨a, b | aba = ba⟩` (`a = 0`, `b = 1` in `Fin 2`).
* `UTEmbeds n` says that `M5` embeds as a semigroup in `UT n`.
-/

namespace M5UT

/-- The max-plus semiring `ℤ̄ = ℤ ∪ {−∞}`. -/
abbrev Zbar := MinTropical (WithTop ℤᵒᵈ)

/-- The integer `a`, viewed as an element of `Zbar`. -/
def zb (a : ℤ) : Zbar := MinTropical.trop ((OrderDual.toDual a : ℤᵒᵈ) : WithTop ℤᵒᵈ)

/-- `−∞`, the adjoined element of `Zbar`. -/
def negInf : Zbar := MinTropical.trop ⊤

/-! ## Sanity lemmas: `Zbar` is max-plus over `ℤ ∪ {−∞}` -/

/-- Addition of integers in `Zbar` is the maximum. -/
theorem zb_add_zb (a b : ℤ) : zb a + zb b = zb (max a b) := by
  unfold zb
  rw [← MinTropical.trop_min]
  congr 1

/-- Multiplication of integers in `Zbar` is the sum. -/
theorem zb_mul_zb (a b : ℤ) : zb a * zb b = zb (a + b) := rfl

/-- The zero of the semiring `Zbar` is `−∞`. -/
theorem zero_eq_negInf : (0 : Zbar) = negInf := rfl

/-- The one of the semiring `Zbar` is the integer `0`. -/
theorem one_eq_zb_zero : (1 : Zbar) = zb 0 := rfl

/-- `−∞` is neutral for `max`. -/
theorem negInf_add (x : Zbar) : negInf + x = x := zero_add x

/-- `−∞` is absorbing for `+`. -/
theorem negInf_mul (x : Zbar) : negInf * x = negInf := zero_mul x

theorem zb_injective : Function.Injective zb := by
  intro a b h
  have h' := congrArg MinTropical.untrop h
  simp only [zb, MinTropical.untrop_trop, WithTop.coe_inj] at h'
  exact OrderDual.toDual_inj.1 h'

theorem zb_ne_negInf (a : ℤ) : zb a ≠ negInf := by
  intro h
  have h' := congrArg MinTropical.untrop h
  simp [zb, negInf] at h'

theorem zb_ne_zero (a : ℤ) : zb a ≠ 0 := zb_ne_negInf a

/-- Every element of `Zbar` is `−∞` or an integer. -/
theorem cases_zb (x : Zbar) : x = negInf ∨ ∃ a : ℤ, x = zb a := by
  induction x using MinTropical.tropRec with
  | h X =>
    induction X using WithTop.recTopCoe with
    | top => exact Or.inl rfl
    | coe y => exact Or.inr ⟨OrderDual.ofDual y, rfl⟩

/-! ## Upper-triangular matrices and the monoid `M5` -/

/-- The subsemigroup `UTₙ(ℤ̄)` of upper-triangular `n × n` matrices over `ℤ̄`:
entries below the diagonal are `−∞` (the zero of `Zbar`). -/
def UT (n : ℕ) : Subsemigroup (Matrix (Fin n) (Fin n) Zbar) where
  carrier := {M | ∀ i j, j < i → M i j = 0}
  mul_mem' := by
    intro M N hM hN i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k i with h | h
    · rw [hM i k h, zero_mul]
    · rw [hN k j (lt_of_lt_of_le hij h), mul_zero]

/-- The defining relation `aba = ba` of `M5`, with `a = 0` and `b = 1`. -/
def rel5 : FreeMonoid (Fin 2) → FreeMonoid (Fin 2) → Prop :=
  fun u v => u = FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 0 ∧
    v = FreeMonoid.of 1 * FreeMonoid.of 0

/-- The monoid `M5 = Mon⟨a, b | aba = ba⟩`. -/
abbrev M5 := PresentedMonoid rel5

/-- `M5` embeds as a (multiplicative) subsemigroup of `UTₙ(ℤ̄)`. -/
def UTEmbeds (n : ℕ) : Prop := ∃ f : M5 →ₙ* UT n, Function.Injective f

/-- Conjecture 2.11 of arXiv:2209.12612: `M5` has UT-rank exactly 4. -/
def Conjecture_2_11 : Prop := UTEmbeds 4 ∧ ∀ n ≤ 3, ¬ UTEmbeds n

end M5UT
```

### `M5Trop.lean`

```lean
import M5Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Arithmetic in the max-plus semiring `Zbar`
-/

namespace M5UT

theorem cases_zb' (x : Zbar) : x = 0 ∨ ∃ a : ℤ, x = zb a := cases_zb x

theorem zb_zero : zb 0 = 1 := rfl

theorem zb_pow (a : ℤ) (n : ℕ) : zb a ^ n = zb (n * a) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; rfl
  | succ n ih =>
    rw [pow_succ, ih, zb_mul_zb]
    congr 1
    push_cast
    ring

theorem zb_add_zb_of_le {a b : ℤ} (h : a ≤ b) : zb a + zb b = zb b := by
  rw [zb_add_zb, max_eq_right h]

theorem zb_add_zb_of_ge {a b : ℤ} (h : b ≤ a) : zb a + zb b = zb a := by
  rw [zb_add_zb, max_eq_left h]

theorem zb_mul_eq_zero {x y : Zbar} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  rcases cases_zb' x with hx | ⟨a, rfl⟩
  · exact Or.inl hx
  rcases cases_zb' y with hy | ⟨b, rfl⟩
  · exact Or.inr hy
  rw [zb_mul_zb] at h
  exact absurd h (zb_ne_zero _)

/-- The tropical binomial identity `(x+y)^(k+1) = x^(k+1) + y (x+y)^k`. -/
theorem trop_binom (x y : Zbar) (k : ℕ) : (x + y) ^ (k + 1) = x ^ (k + 1) + y * (x + y) ^ k := by
  rcases cases_zb' x with rfl | ⟨a, rfl⟩ <;> rcases cases_zb' y with rfl | ⟨b, rfl⟩
  · simp
  · simp [pow_succ']
  · simp
  · rw [zb_add_zb, zb_pow, zb_pow, zb_pow, zb_mul_zb, zb_add_zb]
    congr 1
    push_cast
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      have hk : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
      have : ((k : ℤ) + 1) * a ≤ ((k : ℤ) + 1) * b := mul_le_mul_of_nonneg_left h hk
      rw [max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h]
      rw [max_eq_left (by nlinarith)]

/-- `x` is `−∞` or the integer `0`. -/
def Idem (x : Zbar) : Prop := x = 0 ∨ x = 1

theorem Idem.pow_succ {x : Zbar} (h : Idem x) (k : ℕ) : x ^ (k + 1) = x := by
  rcases h with rfl | rfl
  · simp
  · simp

theorem Idem.add {x y : Zbar} (hx : Idem x) (hy : Idem y) : Idem (x + y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · right; exact MinTropical.add_self 1

theorem Idem.mul {x y : Zbar} (hx : Idem x) (hy : Idem y) : Idem (x * y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · left; simp
  · left; simp
  · left; simp
  · right; simp

theorem idem_zero : Idem 0 := Or.inl rfl

theorem idem_one : Idem 1 := Or.inr rfl

theorem not_idem {x : Zbar} (h : ¬ Idem x) : ∃ e : ℤ, e ≠ 0 ∧ x = zb e := by
  rcases cases_zb' x with hx | ⟨e, rfl⟩
  · exact absurd (Or.inl hx) h
  · refine ⟨e, ?_, rfl⟩
    rintro rfl
    exact h (Or.inr rfl)

theorem Idem.one_add {x : Zbar} (h : Idem x) : 1 + x = 1 := by
  rcases h with rfl | rfl
  · simp
  · exact MinTropical.add_self 1

/-- `(1 + t)^k` splits as `t^k κ + λ` with `κ, λ` independent of `k`. -/
theorem one_add_zb_pow (e : ℤ) : ∃ κ l : Zbar, ∀ k : ℕ, (1 + zb e) ^ k = zb e ^ k * κ + l := by
  rcases le_or_gt e 0 with h | h
  · refine ⟨0, 1, fun k => ?_⟩
    rw [← zb_zero, zb_add_zb_of_ge h, zb_zero]
    simp
  · refine ⟨1, 0, fun k => ?_⟩
    rw [← zb_zero, zb_add_zb_of_le h.le, zb_zero]
    simp

/-- `(t + x)^k` splits as `t^k κ + λ` when `x` is `−∞` or `0`. -/
theorem zb_add_idem_pow (e : ℤ) {x : Zbar} (hx : Idem x) :
    ∃ κ l : Zbar, ∀ k : ℕ, (zb e + x) ^ k = zb e ^ k * κ + l := by
  rcases hx with rfl | rfl
  · exact ⟨1, 0, fun k => by simp⟩
  · rw [add_comm]
    exact one_add_zb_pow e

end M5UT
```

### `M5Normal.lean`

```lean
import M5Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic.FinCases

/-!
# Normal forms in `M5`

Every element of `M5 = Mon⟨a, b | aba = ba⟩` equals `N α β γ = (ba)^α a^β b^γ`
(right multiplication rules: `N·b = N(α,β,γ+1)`, `N(α,β,0)·a = N(α,β+1,0)`,
`N(α,β,γ+1)·a = N(α+γ+1,0,0)`).  Distinctness of the `N α β γ` is proved later
from the faithful `UT₄` representation.
-/

namespace M5UT

/-- The generator `a`. -/
abbrev ga : M5 := PresentedMonoid.of rel5 0
/-- The generator `b`. -/
abbrev gb : M5 := PresentedMonoid.of rel5 1

theorem rel_M5 : ga * gb * ga = gb * ga := by
  have h := PresentedMonoid.mk_eq_mk_of_rel (rels := rel5)
    (x := FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 0)
    (y := FreeMonoid.of 1 * FreeMonoid.of 0) ⟨rfl, rfl⟩
  rw [map_mul, map_mul, map_mul] at h
  exact h

/-- The normal form `(ba)^α a^β b^γ`. -/
def N (α β γ : ℕ) : M5 := (gb * ga) ^ α * ga ^ β * gb ^ γ

theorem a_ba : ga * (gb * ga) = gb * ga := by rw [← mul_assoc, rel_M5]

theorem b_ba : gb * (gb * ga) = (gb * ga) * (gb * ga) := by
  calc gb * (gb * ga) = gb * (ga * gb * ga) := by rw [rel_M5]
    _ = gb * ga * (gb * ga) := by simp only [mul_assoc]

theorem pow_a_ba (β k : ℕ) : ga ^ β * (gb * ga) ^ (k + 1) = (gb * ga) ^ (k + 1) := by
  induction β with
  | zero => simp
  | succ β ih =>
    rw [pow_succ, mul_assoc, pow_succ' (gb * ga) k, ← mul_assoc ga, a_ba, ← pow_succ', ih]

theorem pow_b_ba (γ k : ℕ) : gb ^ γ * (gb * ga) ^ (k + 1) = (gb * ga) ^ (k + 1 + γ) := by
  induction γ generalizing k with
  | zero => simp
  | succ γ ih =>
    rw [pow_succ, mul_assoc, pow_succ' (gb * ga) k, ← mul_assoc gb, b_ba, mul_assoc,
      ← pow_succ', ← pow_succ', ih]
    congr 1
    omega

theorem N_mul_b (α β γ : ℕ) : N α β γ * gb = N α β (γ + 1) := by
  simp only [N, pow_succ, mul_assoc]

theorem N_zero_mul_a (α β : ℕ) : N α β 0 * ga = N α (β + 1) 0 := by
  simp only [N, pow_zero, mul_one, pow_succ, mul_assoc]

theorem N_succ_mul_a (α β γ : ℕ) : N α β (γ + 1) * ga = N (α + γ + 1) 0 0 := by
  have h1 : gb ^ (γ + 1) * ga = gb ^ γ * (gb * ga) ^ (0 + 1) := by
    rw [pow_succ, zero_add, pow_one, mul_assoc]
  have h2 : N α β (γ + 1) * ga = (gb * ga) ^ α * (ga ^ β * (gb ^ γ * (gb * ga) ^ (0 + 1))) := by
    rw [← h1]; simp only [N, mul_assoc]
  rw [h2, pow_b_ba, show 0 + 1 + γ = γ + 1 by omega, pow_a_ba, ← pow_add]
  simp only [N, pow_zero, mul_one]
  congr 1

/-- Every element of `M5` is a normal form. -/
theorem exists_N (x : M5) : ∃ α β γ : ℕ, x = N α β γ := by
  induction x using Submonoid.induction_of_closure_eq_top_right
    (PresentedMonoid.closure_range_of rel5) with
  | one => exact ⟨0, 0, 0, by simp [N]⟩
  | mul_right x y hy ih =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨α, β, γ, rfl⟩ := ih
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · cases γ with
      | zero => exact ⟨α, β + 1, 0, N_zero_mul_a α β⟩
      | succ γ => exact ⟨α + γ + 1, 0, 0, N_succ_mul_a α β γ⟩
    · exact ⟨α, β, γ + 1, N_mul_b α β γ⟩

/-! ## Semigroup homomorphisms into `UT n` -/

section Hom

variable {n : ℕ} (f : M5 →ₙ* UT n)

theorem hom_mul (x y : M5) :
    ((f (x * y) : UT n) : Matrix (Fin n) (Fin n) Zbar) = (f x : Matrix _ _ _) * (f y : Matrix _ _ _) := by
  rw [map_mul]; rfl

theorem hom_pow (x : M5) (k : ℕ) :
    ((f (x ^ (k + 1)) : UT n) : Matrix (Fin n) (Fin n) Zbar) = (f x : Matrix _ _ _) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ x, hom_mul, ih, ← pow_succ]

theorem hom_N (α β γ : ℕ) :
    ((f (N (α + 1) (β + 1) (γ + 1)) : UT n) : Matrix (Fin n) (Fin n) Zbar) =
      ((f gb : Matrix _ _ _) * (f ga : Matrix _ _ _)) ^ (α + 1) * (f ga : Matrix _ _ _) ^ (β + 1) *
        (f gb : Matrix _ _ _) ^ (γ + 1) := by
  rw [N, hom_mul, hom_mul, hom_pow, hom_pow, hom_pow, hom_mul]

theorem hom_rel :
    (f ga : Matrix (Fin n) (Fin n) Zbar) * (f gb : Matrix _ _ _) * (f ga : Matrix _ _ _) =
      (f gb : Matrix _ _ _) * (f ga : Matrix _ _ _) := by
  rw [← hom_mul, ← hom_mul, ← hom_mul, rel_M5]

end Hom

end M5UT
```

### `M5UT4Pow.lean`

```lean
import M5Trop
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin

/-!
# The corrected `UT₄` matrices of Lemma 2.9 and their powers

The source (arXiv:2209.12612, Lemma 2.9) prints `B₁₁ = 1`; with that value the map is not
injective.  We use the corrected value `B₁₁ = −1` (row/column indices start at 1 in the
source, at 0 in Lean).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

/-- The image of `a`. -/
def A4 : Matrix (Fin 4) (Fin 4) Zbar :=
  !![zb 0, zb 1, 0, zb 0;
     0, zb 1, zb 0, zb (-1);
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The image of `b` (source's `B` with the misprint `B₁₁ = 1` corrected to `−1`). -/
def B4 : Matrix (Fin 4) (Fin 4) Zbar :=
  !![zb (-1), zb 0, zb 0, zb (-1);
     0, 0, 0, zb 0;
     0, 0, zb 0, 0;
     0, 0, 0, zb 1]

/-- `BA`. -/
def C4 : Matrix (Fin 4) (Fin 4) Zbar :=
  !![zb (-1), zb 1, zb 0, zb (-1);
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

theorem B4_mul_A4 : B4 * A4 = C4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B4, A4, C4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]

theorem A4_mul_C4 : A4 * C4 = C4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A4, C4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]

/-- The relation `ABA = BA` holds for the corrected matrices. -/
theorem A4_B4_rel : A4 * B4 * A4 = B4 * A4 := by
  rw [mul_assoc, B4_mul_A4, A4_mul_C4]

theorem C4_pow (n : ℕ) : C4 ^ (n + 1) =
    !![zb (-(n + 1)), zb (-(n + 1) + 2), zb (-(n + 1) + 1), zb (-(n + 1));
       0, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, 0] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [C4]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb] <;>
      (congr 1 <;> push_cast <;> omega)

theorem A4_pow (n : ℕ) : A4 ^ (n + 2) =
    !![zb 0, zb (n + 2), zb (n + 1), zb n;
       0, zb (n + 2), zb (n + 1), zb n;
       0, 0, 0, 0;
       0, 0, 0, 0] := by
  induction n with
  | zero =>
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb] <;>
      (congr 1 <;> push_cast <;> omega)

theorem B4_pow (n : ℕ) : B4 ^ (n + 1) =
    !![zb (-(n + 1)), zb (-n), zb 0, zb (n - 1);
       0, 0, 0, zb n;
       0, 0, zb 0, 0;
       0, 0, 0, zb (n + 1)] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B4]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb] <;>
      (congr 1 <;> push_cast <;> omega)

end M5UT
```

### `M5UT4.lean`

```lean
import M5UT4Pow
import M5Normal

/-!
# `M5` embeds in `UT₄(ℤ̄)` (source Lemma 2.9, with the misprint `B₁₁ = 1` corrected to `−1`)

`a ↦ A4`, `b ↦ B4` respects `aba = ba`; the image of the normal form `N α β γ` is
`X4 α β γ = C4^α A4^β B4^γ`, and `dec` recovers `(α, β, γ)` from it.  With the spanning
lemma `exists_N` this gives injectivity, and also that the normal forms are pairwise
distinct in `M5`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

/-- Images of the generators. -/
def gen4 : Fin 2 → Matrix (Fin 4) (Fin 4) Zbar := ![A4, B4]

/-- The monoid homomorphism `M5 → Mat₄(ℤ̄)`, `a ↦ A4`, `b ↦ B4`. -/
def psi4 : M5 →* Matrix (Fin 4) (Fin 4) Zbar :=
  PresentedMonoid.lift gen4 (by
    rintro u v ⟨rfl, rfl⟩
    simp only [map_mul, FreeMonoid.lift_eval_of]
    exact A4_B4_rel)

theorem psi4_a : psi4 ga = A4 := rfl

theorem psi4_b : psi4 gb = B4 := rfl

/-- The image of the normal form `N α β γ`. -/
def X4 (α β γ : ℕ) : Matrix (Fin 4) (Fin 4) Zbar := C4 ^ α * A4 ^ β * B4 ^ γ

theorem psi4_N (α β γ : ℕ) : psi4 (N α β γ) = X4 α β γ := by
  simp only [N, X4, map_mul, map_pow, psi4_a, psi4_b, B4_mul_A4]

/-- Integer value of an element of `Zbar` (junk value `0` at `−∞`). -/
def ev (x : Zbar) : ℤ := OrderDual.ofDual ((MinTropical.untrop x).untopD (OrderDual.toDual 0))

@[simp] theorem ev_zb (a : ℤ) : ev (zb a) = a := rfl

/-- Decoding the exponents from the image matrix. -/
noncomputable def dec (X : Matrix (Fin 4) (Fin 4) Zbar) : ℕ × ℕ × ℕ :=
  if X 2 2 = 0 then
    if X 1 2 = 0 then
      ((-ev (X 0 0) - (ev (X 0 3) - ev (X 0 2)).toNat).toNat,
        (ev (X 0 2) + (-ev (X 0 0) - (ev (X 0 3) - ev (X 0 2)).toNat) - 1).toNat,
        (ev (X 0 3) - ev (X 0 2)).toNat)
    else (0, (ev (X 1 2) + 1).toNat, (-ev (X 0 0)).toNat)
  else (0, 0, (ev (X 3 3)).toNat)

attribute [local simp] zb_ne_zero

theorem A4_pow' (n : ℕ) : A4 ^ (n + 1 + 1) =
    !![zb 0, zb (n + 2), zb (n + 1), zb n;
       0, zb (n + 2), zb (n + 1), zb n;
       0, 0, 0, 0;
       0, 0, 0, 0] := A4_pow n

theorem dec_X4 (α β γ : ℕ) : dec (X4 α β γ) = (α, β, γ) := by
  rcases α with _ | k <;> rcases β with _ | _ | m <;> rcases γ with _ | n
  · simp [X4, dec, ← zb_zero]
  · simp [X4, dec, B4_pow]
  · simp [X4, dec, A4]
  · simp [X4, dec, B4_pow, A4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
  · simp [X4, dec, A4_pow']
    omega
  · simp [X4, dec, B4_pow, A4_pow', Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
    omega
  · simp [X4, dec, C4_pow]
  · simp [X4, dec, C4_pow, B4_pow, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
    omega
  · simp [X4, dec, C4_pow, A4, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
    omega
  · simp [X4, dec, C4_pow, A4, B4_pow, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
    omega
  · simp [X4, dec, C4_pow, A4_pow', Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]
    omega
  · simp [X4, dec, C4_pow, A4_pow', B4_pow, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb,
      zb_add_zb]
    omega

/-- The normal forms are pairwise distinct (Shneerson's normal form, source Lemma 2.8). -/
theorem N_injective {α β γ α' β' γ' : ℕ} (h : N α β γ = N α' β' γ') :
    (α, β, γ) = (α', β', γ') := by
  have h' := congrArg (fun x => dec (psi4 x)) h
  simp only [psi4_N, dec_X4] at h'
  exact h'

theorem psi4_injective : Function.Injective psi4 := by
  intro x y h
  obtain ⟨α, β, γ, rfl⟩ := exists_N x
  obtain ⟨α', β', γ', rfl⟩ := exists_N y
  rw [psi4_N, psi4_N] at h
  have h' := congrArg dec h
  rw [dec_X4, dec_X4] at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl⟩ := h'
  rfl

theorem one_mem_UT (n : ℕ) : (1 : Matrix (Fin n) (Fin n) Zbar) ∈ UT n := by
  intro i j hij
  exact Matrix.one_apply_ne (ne_of_lt hij).symm

theorem pow_mem_UT {n : ℕ} {M : Matrix (Fin n) (Fin n) Zbar} (hM : M ∈ UT n) (k : ℕ) :
    M ^ k ∈ UT n := by
  induction k with
  | zero => exact one_mem_UT n
  | succ k ih => rw [pow_succ]; exact (UT n).mul_mem ih hM

theorem A4_mem : A4 ∈ UT 4 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [A4]

theorem B4_mem : B4 ∈ UT 4 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [B4]

theorem psi4_mem (x : M5) : psi4 x ∈ UT 4 := by
  obtain ⟨α, β, γ, rfl⟩ := exists_N x
  rw [psi4_N, X4, ← B4_mul_A4]
  exact (UT 4).mul_mem ((UT 4).mul_mem (pow_mem_UT ((UT 4).mul_mem B4_mem A4_mem) α)
    (pow_mem_UT A4_mem β)) (pow_mem_UT B4_mem γ)

/-- The semigroup embedding `M5 → UT₄(ℤ̄)`. -/
def f4 : M5 →ₙ* UT 4 where
  toFun x := ⟨psi4 x, psi4_mem x⟩
  map_mul' x y := Subtype.ext (map_mul psi4 x y)

theorem f4_injective : Function.Injective f4 := by
  intro x y h
  exact psi4_injective (congrArg Subtype.val h)

theorem UTEmbeds_four : UTEmbeds 4 := ⟨f4, f4_injective⟩

end M5UT
```

### `M5Pow3.lean`

```lean
import M5Trop
import M5UT4
import Mathlib.Algebra.BigOperators.Fin

/-!
# Powers of upper-triangular `3 × 3` matrices over `Zbar`

Explicit formulas (valid for every exponent `k + 1`):
* `(M^(k+1))ᵢᵢ = Mᵢᵢ^(k+1)`,
* `(M^(k+1))₀₁ = M₀₁ (M₀₀ + M₁₁)^k`, `(M^(k+1))₁₂ = M₁₂ (M₁₁ + M₂₂)^k`,
* `(M^(k+1))₀₂ = M₀₂ (M₀₀ + M₂₂)^k + M₀₁ M₁₂ corner k`, where `corner 0 = −∞` and
  `corner (k+1) = (M₀₀ + M₁₁ + M₂₂)^k`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

/-- The path sum for the corner entry. -/
def corner (x y z : Zbar) : ℕ → Zbar
  | 0 => 0
  | k + 1 => (x + y + z) ^ k

theorem corner_succ (x y z : Zbar) (k : ℕ) :
    corner x y z (k + 1) = (x + y) ^ k + z * corner x y z k := by
  cases k with
  | zero => simp [corner]
  | succ k => simp only [corner]; exact trop_binom (x + y) z k

theorem UT3_10 {M : Matrix (Fin 3) (Fin 3) Zbar} (hM : M ∈ UT 3) : M 1 0 = 0 := hM 1 0 (by decide)
theorem UT3_20 {M : Matrix (Fin 3) (Fin 3) Zbar} (hM : M ∈ UT 3) : M 2 0 = 0 := hM 2 0 (by decide)
theorem UT3_21 {M : Matrix (Fin 3) (Fin 3) Zbar} (hM : M ∈ UT 3) : M 2 1 = 0 := hM 2 1 (by decide)

theorem pow3 {M : Matrix (Fin 3) (Fin 3) Zbar} (hM : M ∈ UT 3) (k : ℕ) :
    (M ^ (k + 1)) 0 0 = M 0 0 ^ (k + 1) ∧ (M ^ (k + 1)) 1 1 = M 1 1 ^ (k + 1) ∧
    (M ^ (k + 1)) 2 2 = M 2 2 ^ (k + 1) ∧
    (M ^ (k + 1)) 0 1 = M 0 1 * (M 0 0 + M 1 1) ^ k ∧
    (M ^ (k + 1)) 1 2 = M 1 2 * (M 1 1 + M 2 2) ^ k ∧
    (M ^ (k + 1)) 0 2 = M 0 2 * (M 0 0 + M 2 2) ^ k + M 0 1 * M 1 2 * corner (M 0 0) (M 1 1) (M 2 2) k := by
  have h10 := UT3_10 hM
  have h20 := UT3_20 hM
  have h21 := UT3_21 hM
  induction k with
  | zero => simp [corner]
  | succ k ih =>
    obtain ⟨i00, i11, i22, i01, i12, i02⟩ := ih
    have hP := pow_mem_UT hM (k + 1)
    have p10 := UT3_10 hP
    have p20 := UT3_20 hP
    have p21 := UT3_21 hP
    rw [pow_succ M (k + 1)]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, i00, i11, i22, i01, i12, i02, p10, p20, p21,
      h10, h20, h21, zero_mul, mul_zero, add_zero, zero_add]
    refine ⟨by ring, by ring, by ring, ?_, ?_, ?_⟩
    · rw [trop_binom]; ring
    · rw [trop_binom]; ring
    · rw [trop_binom (M 0 0) (M 2 2), corner_succ]; ring

/-- Diagonal of a product of upper-triangular `3 × 3` matrices. -/
theorem diag_mul3 {M P : Matrix (Fin 3) (Fin 3) Zbar} (hM : M ∈ UT 3) (hP : P ∈ UT 3) (i : Fin 3) :
    (M * P) i i = M i i * P i i := by
  have h10 := UT3_10 hM
  have h20 := UT3_20 hM
  have h21 := UT3_21 hM
  have g10 := UT3_10 hP
  have g20 := UT3_20 hP
  have g21 := UT3_21 hP
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, g10, g20, g21]

/-- Termwise invariance of a triple product. -/
theorem mul3_congr {n : ℕ} (C A A' B : Matrix (Fin n) (Fin n) Zbar)
    (h : ∀ p q, A p q = A' p q ∨ (∀ i, C i p = 0) ∨ (∀ j, B q j = 0)) :
    C * A * B = C * A' * B := by
  ext i j
  simp only [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  rcases h p q with h | h | h
  · rw [h]
  · rw [h i]; simp
  · rw [h j]; simp

end M5UT
```

### `M5Collide.lean`

```lean
import M5Trop
import Mathlib.Data.Matrix.Mul

/-!
# The collision lemma (Case II of the lower bound)

Suppose a family of `3 × 3` matrices `X α β γ` has, for `α, γ ≥ 1` and `β ≥ 2`,
all entries other than `(0,2)` depending only on `α + γ`, and
`X₀₂ = (α' b₁ + β' e + γ' b₃) ⊗ K* ⊕ G(α', γ')` (shifted exponents `α', β', γ'`),
with `e ≠ 0` an integer.  Then two distinct exponent triples give the same matrix.
Integrality enters through the integer shift `(α + e, β − d, γ − e)`, `d = b₁ − b₃`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

theorem dominate (x : Zbar) : ∃ N : ℤ, ∀ y : ℤ, N ≤ y → x + zb y = zb y := by
  rcases cases_zb' x with rfl | ⟨g, rfl⟩
  · exact ⟨0, fun y _ => zero_add _⟩
  · exact ⟨g, fun y hy => zb_add_zb_of_le hy⟩

theorem collide (X : ℕ → ℕ → ℕ → Matrix (Fin 3) (Fin 3) Zbar) (e b1 b3 : ℤ) (he : e ≠ 0)
    (Ks : Zbar) (h : Fin 3 → Fin 3 → ℕ → Zbar) (G : ℕ → ℕ → Zbar)
    (hX : ∀ α β γ : ℕ,
      (∀ i j, ¬ (i = 0 ∧ j = 2) → X (α + 1) (β + 2) (γ + 1) i j = h i j (α + γ)) ∧
      X (α + 1) (β + 2) (γ + 1) 0 2 = zb (α * b1 + β * e + γ * b3) * Ks + G α γ) :
    ∃ α β γ α' β' γ' : ℕ, (α, β, γ) ≠ (α', β', γ') ∧
      X (α + 1) (β + 1) (γ + 1) = X (α' + 1) (β' + 1) (γ' + 1) := by
  have eqX : ∀ α β γ α' β' γ' : ℕ, α + γ = α' + γ' →
      X (α + 1) (β + 2) (γ + 1) 0 2 = X (α' + 1) (β' + 2) (γ' + 1) 0 2 →
      X (α + 1) (β + 2) (γ + 1) = X (α' + 1) (β' + 2) (γ' + 1) := by
    intro α β γ α' β' γ' hs h02
    ext i j
    by_cases hij : i = 0 ∧ j = 2
    · obtain ⟨rfl, rfl⟩ := hij
      exact h02
    · rw [(hX α β γ).1 i j hij, (hX α' β' γ').1 i j hij, hs]
  rcases cases_zb' Ks with hK | ⟨k, rfl⟩
  · -- `K* = −∞`: no entry depends on `β`.
    refine ⟨2, 2, 2, 2, 3, 2, by simp, ?_⟩
    exact eqX 2 1 2 2 2 2 rfl (by rw [(hX 2 1 2).2, (hX 2 2 2).2, hK]; simp)
  rcases lt_or_gt_of_ne he with hneg | hpos
  · -- `e < 0`
    obtain ⟨E, hE⟩ : ∃ E : ℕ, (E : ℤ) = -e := ⟨(-e).toNat, by omega⟩
    have hE1 : 1 ≤ E := by omega
    -- `β` becomes invisible at a point where `G` is finite.
    have invisible : ∀ α γ : ℕ, G α γ ≠ 0 →
        ∃ β : ℕ, X (α + 1) (β + 2) (γ + 1) = X (α + 1) (β + 1 + 2) (γ + 1) := by
      intro α γ hG
      obtain ⟨g, hg⟩ : ∃ g, G α γ = zb g := by
        rcases cases_zb' (G α γ) with h0 | h1
        · exact absurd h0 hG
        · exact h1
      refine ⟨((α : ℤ) * b1 + γ * b3 + k - g).toNat, ?_⟩
      apply eqX _ _ _ _ _ _ rfl
      rw [(hX _ _ _).2, (hX _ _ _).2, hg, zb_mul_zb, zb_mul_zb, zb_add_zb_of_le, zb_add_zb_of_le]
      · set β : ℕ := ((α : ℤ) * b1 + γ * b3 + k - g).toNat with hβ
        have h1 : ((β + 1 : ℕ) : ℤ) * e ≤ -((β + 1 : ℕ) : ℤ) := by
          have := mul_le_mul_of_nonneg_left (show e ≤ -1 by omega)
            (Int.natCast_nonneg (β + 1))
          linarith
        push_cast at h1 ⊢
        omega
      · set β : ℕ := ((α : ℤ) * b1 + γ * b3 + k - g).toNat with hβ
        have h1 : (β : ℤ) * e ≤ -(β : ℤ) := by
          have := mul_le_mul_of_nonneg_left (show e ≤ -1 by omega) (Int.natCast_nonneg β)
          linarith
        omega
    by_cases g1 : G (1 + E) 1 = 0
    · by_cases g2 : G 1 (1 + E) = 0
      · -- `X₀₂ = F` at both shift points: integer shift.
        refine ⟨1 + E, (b1 - b3).toNat + 1, 1, 1, (-(b1 - b3)).toNat + 1, 1 + E,
          by simp; omega, ?_⟩
        apply eqX _ _ _ _ _ _ (by omega)
        rw [(hX _ _ _).2, (hX _ _ _).2, g1, g2, add_zero, add_zero]
        congr 2
        push_cast
        have hd : ((b1 - b3).toNat : ℤ) = ((-(b1 - b3)).toNat : ℤ) + (b1 - b3) := by omega
        rw [hd, hE]
        ring
      · obtain ⟨β, hβ⟩ := invisible 1 (1 + E) g2
        exact ⟨1, β + 1, 1 + E, 1, β + 1 + 1, 1 + E, by simp, hβ⟩
    · obtain ⟨β, hβ⟩ := invisible (1 + E) 1 g1
      exact ⟨1 + E, β + 1, 1, 1 + E, β + 1 + 1, 1, by simp, hβ⟩
  · -- `e > 0`: `F` dominates for `β` large at both shift points.
    obtain ⟨E, hE⟩ : ∃ E : ℕ, (E : ℤ) = e := ⟨e.toNat, by omega⟩
    have hE1 : 1 ≤ E := by omega
    obtain ⟨N1, hN1⟩ := dominate (G 1 (1 + E))
    obtain ⟨N2, hN2⟩ := dominate (G (1 + E) 1)
    set d : ℤ := b1 - b3 with hd
    set c : ℤ := (1 + E) * b1 + b3 + k with hc
    set M : ℕ := d.toNat + (-d).toNat + N1.toNat + N2.toNat + (-c).toNat with hM
    have hMe : (M : ℤ) ≤ M * e := le_mul_of_one_le_right (Int.natCast_nonneg M) (by omega)
    have hP : (((M : ℤ) + d).toNat : ℤ) = M + d := by omega
    have hF1 : ((1 : ℕ) : ℤ) * b1 + (((M : ℤ) + d).toNat : ℤ) * e + ((1 + E : ℕ) : ℤ) * b3 + k
        = c + M * e := by
      rw [hP, hc, hd]; push_cast; rw [hE]; ring
    have hF2 : ((1 + E : ℕ) : ℤ) * b1 + (M : ℤ) * e + ((1 : ℕ) : ℤ) * b3 + k = c + M * e := by
      rw [hc]; push_cast; ring
    refine ⟨1, ((M : ℤ) + d).toNat + 1, 1 + E, 1 + E, M + 1, 1, by simp; omega, ?_⟩
    apply eqX _ _ _ _ _ _ (by omega)
    rw [(hX _ _ _).2, (hX _ _ _).2, zb_mul_zb, zb_mul_zb, hF1, hF2,
      add_comm (zb _) (G 1 (1 + E)), add_comm (zb _) (G (1 + E) 1), hN1, hN2]
    · omega
    · omega

end M5UT
```

### `M5Lower3.lean`

```lean
import M5Pow3
import M5Collide

/-!
# Lower bound in dimension 3

For upper-triangular `A, B ∈ UT₃(ℤ̄)` with `ABA = BA`, two distinct exponent triples
`(α, β, γ) ≠ (α', β', γ')` (all exponents `≥ 1`) give equal products
`(BA)^α A^β B^γ = (BA)^α' A^β' B^γ'`.

Diagonal constraints (from the diagonal of `A(BA) = BA`): if `aᵢ ∉ {−∞, 0}` then
`cᵢ = bᵢ = −∞`; if `cᵢ ≠ −∞` then `aᵢ = 0`.

* If `a₁ ∈ {−∞, 0}`, or `c₀ = −∞`, or `b₂ = −∞`: the product is termwise independent of
  `β ≥ 3`, so `(3,3,3)` and `(3,4,3)` collide.
* Otherwise (`a₁ = e ≠ 0`, `c₀ = b₀`, `b₂` finite, `a₀ = 0`, `a₂ ∈ {−∞, 0}`):
  `A^(β+2) = e^β K + L`, and the collision lemma applies.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

/-- The image of the normal form `(ba)^α a^β b^γ` when `a ↦ A`, `b ↦ B`. -/
def X3 (A B : Matrix (Fin 3) (Fin 3) Zbar) (α β γ : ℕ) : Matrix (Fin 3) (Fin 3) Zbar :=
  (B * A) ^ α * A ^ β * B ^ γ

theorem Idem.pow_of_ne_zero {x : Zbar} (h : Idem x) {k : ℕ} (hk : k ≠ 0) : x ^ k = x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact h.pow_succ j

section Lower

variable {A B : Matrix (Fin 3) (Fin 3) Zbar}

theorem diag_rel (hA : A ∈ UT 3) (hB : B ∈ UT 3) (hrel : A * B * A = B * A) (i : Fin 3) :
    A i i * (B * A) i i = (B * A) i i := by
  rw [← diag_mul3 hA ((UT 3).mul_mem hB hA) i, ← mul_assoc, hrel]

theorem diag_cases (hA : A ∈ UT 3) (hB : B ∈ UT 3) (hrel : A * B * A = B * A) (i : Fin 3) :
    Idem (A i i) ∨ ((B * A) i i = 0 ∧ B i i = 0) := by
  have h1 : (B * A) i i = B i i * A i i := diag_mul3 hB hA i
  have h2 := diag_rel hA hB hrel i
  by_cases hi : Idem (A i i)
  · exact Or.inl hi
  right
  obtain ⟨e, he, hae⟩ := not_idem hi
  rcases cases_zb' ((B * A) i i) with hc | ⟨c, hc⟩
  · refine ⟨hc, ?_⟩
    rw [hc, hae] at h1
    rcases zb_mul_eq_zero h1.symm with h | h
    · exact h
    · exact absurd h (zb_ne_zero e)
  · exfalso
    rw [hc, hae, zb_mul_zb] at h2
    have := zb_injective h2
    omega

theorem diag_one (hA : A ∈ UT 3) (hB : B ∈ UT 3) (hrel : A * B * A = B * A) (i : Fin 3)
    (hc : (B * A) i i ≠ 0) : A i i = 1 := by
  have h2 := diag_rel hA hB hrel i
  rcases cases_zb' (A i i) with ha | ⟨e, ha⟩
  · rw [ha, zero_mul] at h2
    exact absurd h2.symm hc
  rcases cases_zb' ((B * A) i i) with hc' | ⟨c, hc'⟩
  · exact absurd hc' hc
  rw [ha, hc', zb_mul_zb] at h2
  have := zb_injective h2
  rw [ha, show e = 0 by omega]
  rfl

/-- The invariant case: the product does not depend on `β ∈ {3, 4}`. -/
theorem invariant_case (hA : A ∈ UT 3) (hB : B ∈ UT 3) (hrel : A * B * A = B * A)
    (h : Idem (A 1 1) ∨ (B * A) 0 0 = 0 ∨ B 2 2 = 0) :
    X3 A B (2 + 1) (2 + 1) (2 + 1) = X3 A B (2 + 1) (3 + 1) (2 + 1) := by
  have hC := (UT 3).mul_mem hB hA
  obtain ⟨p00, p11, p22, p01, p12, p02⟩ := pow3 hA 2
  obtain ⟨q00, q11, q22, q01, q12, q02⟩ := pow3 hA 3
  have l3 := pow_mem_UT hA (2 + 1)
  have l4 := pow_mem_UT hA (3 + 1)
  have e00 : Idem (A 0 0) → (A ^ (2 + 1)) 0 0 = (A ^ (3 + 1)) 0 0 := fun h => by
    rw [p00, q00, h.pow_succ, h.pow_succ]
  have e11 : Idem (A 1 1) → (A ^ (2 + 1)) 1 1 = (A ^ (3 + 1)) 1 1 := fun h => by
    rw [p11, q11, h.pow_succ, h.pow_succ]
  have e22 : Idem (A 2 2) → (A ^ (2 + 1)) 2 2 = (A ^ (3 + 1)) 2 2 := fun h => by
    rw [p22, q22, h.pow_succ, h.pow_succ]
  have e01 : Idem (A 0 0) → Idem (A 1 1) → (A ^ (2 + 1)) 0 1 = (A ^ (3 + 1)) 0 1 :=
    fun h0 h1 => by
      rw [p01, q01, (h0.add h1).pow_of_ne_zero (by norm_num),
        (h0.add h1).pow_of_ne_zero (by norm_num)]
  have e12 : Idem (A 1 1) → Idem (A 2 2) → (A ^ (2 + 1)) 1 2 = (A ^ (3 + 1)) 1 2 :=
    fun h1 h2 => by
      rw [p12, q12, (h1.add h2).pow_of_ne_zero (by norm_num),
        (h1.add h2).pow_of_ne_zero (by norm_num)]
  have e02 : Idem (A 0 0) → Idem (A 1 1) → Idem (A 2 2) →
      (A ^ (2 + 1)) 0 2 = (A ^ (3 + 1)) 0 2 := fun h0 h1 h2 => by
    rw [p02, q02]
    simp only [corner, pow_one]
    rw [(h0.add h2).pow_of_ne_zero (k := 2) (by norm_num),
      (h0.add h2).pow_of_ne_zero (k := 3) (by norm_num),
      ((h0.add h1).add h2).pow_of_ne_zero (k := 2) (by norm_num)]
  have e10 : (A ^ (2 + 1)) 1 0 = (A ^ (3 + 1)) 1 0 := by rw [UT3_10 l3, UT3_10 l4]
  have e20 : (A ^ (2 + 1)) 2 0 = (A ^ (3 + 1)) 2 0 := by rw [UT3_20 l3, UT3_20 l4]
  have e21 : (A ^ (2 + 1)) 2 1 = (A ^ (3 + 1)) 2 1 := by rw [UT3_21 l3, UT3_21 l4]
  -- zero columns of `(BA)^3` and zero rows of `B^3`
  obtain ⟨c00, c11, -, c01, -, -⟩ := pow3 hC 2
  obtain ⟨b00, b11, b22, b01, b12, -⟩ := pow3 hB 2
  have lc := pow_mem_UT hC (2 + 1)
  have lb := pow_mem_UT hB (2 + 1)
  have colz0 : (B * A) 0 0 = 0 → ∀ i, ((B * A) ^ (2 + 1)) i 0 = 0 := by
    intro hc i
    fin_cases i
    · simp [c00, hc]
    · exact UT3_10 lc
    · exact UT3_20 lc
  have colz1 : (B * A) 0 0 = 0 → (B * A) 1 1 = 0 → ∀ i, ((B * A) ^ (2 + 1)) i 1 = 0 := by
    intro hc0 hc1 i
    fin_cases i
    · simp [c01, hc0, hc1]
    · simp [c11, hc1]
    · exact UT3_21 lc
  have rowz2 : B 2 2 = 0 → ∀ j, (B ^ (2 + 1)) 2 j = 0 := by
    intro hb j
    fin_cases j
    · exact UT3_20 lb
    · exact UT3_21 lb
    · simp [b22, hb]
  have rowz1 : B 1 1 = 0 → B 2 2 = 0 → ∀ j, (B ^ (2 + 1)) 1 j = 0 := by
    intro hb1 hb2 j
    fin_cases j
    · exact UT3_10 lb
    · simp [b11, hb1]
    · simp [b12, hb1, hb2]
  have F0 : Idem (A 0 0) ∨ ∀ i, ((B * A) ^ (2 + 1)) i 0 = 0 := by
    rcases diag_cases hA hB hrel 0 with h | h
    · exact Or.inl h
    · exact Or.inr (colz0 h.1)
  have F2 : Idem (A 2 2) ∨ ∀ j, (B ^ (2 + 1)) 2 j = 0 := by
    rcases diag_cases hA hB hrel 2 with h | h
    · exact Or.inl h
    · exact Or.inr (rowz2 h.2)
  unfold X3
  apply mul3_congr
  intro p q
  rcases h with h1 | hc0 | hb2
  · fin_cases p <;> fin_cases q
    · rcases F0 with h | h
      · exact Or.inl (e00 h)
      · exact Or.inr (Or.inl h)
    · rcases F0 with h | h
      · exact Or.inl (e01 h h1)
      · exact Or.inr (Or.inl h)
    · rcases F0 with h | h
      · rcases F2 with h' | h'
        · exact Or.inl (e02 h h1 h')
        · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl h)
    · exact Or.inl e10
    · exact Or.inl (e11 h1)
    · rcases F2 with h' | h'
      · exact Or.inl (e12 h1 h')
      · exact Or.inr (Or.inr h')
    · exact Or.inl e20
    · exact Or.inl e21
    · rcases F2 with h' | h'
      · exact Or.inl (e22 h')
      · exact Or.inr (Or.inr h')
  · by_cases h1 : Idem (A 1 1)
    · -- already covered by the first alternative; redo it
      fin_cases p <;> fin_cases q
      · exact Or.inr (Or.inl (colz0 hc0))
      · exact Or.inr (Or.inl (colz0 hc0))
      · exact Or.inr (Or.inl (colz0 hc0))
      · exact Or.inl e10
      · exact Or.inl (e11 h1)
      · rcases F2 with h' | h'
        · exact Or.inl (e12 h1 h')
        · exact Or.inr (Or.inr h')
      · exact Or.inl e20
      · exact Or.inl e21
      · rcases F2 with h' | h'
        · exact Or.inl (e22 h')
        · exact Or.inr (Or.inr h')
    · have hc1 : (B * A) 1 1 = 0 := by
        rcases diag_cases hA hB hrel 1 with h | h
        · exact absurd h h1
        · exact h.1
      fin_cases p <;> fin_cases q
      · exact Or.inr (Or.inl (colz0 hc0))
      · exact Or.inr (Or.inl (colz0 hc0))
      · exact Or.inr (Or.inl (colz0 hc0))
      · exact Or.inr (Or.inl (colz1 hc0 hc1))
      · exact Or.inr (Or.inl (colz1 hc0 hc1))
      · exact Or.inr (Or.inl (colz1 hc0 hc1))
      · exact Or.inl e20
      · exact Or.inl e21
      · rcases F2 with h' | h'
        · exact Or.inl (e22 h')
        · exact Or.inr (Or.inr h')
  · by_cases h1 : Idem (A 1 1)
    · fin_cases p <;> fin_cases q
      · rcases F0 with h | h
        · exact Or.inl (e00 h)
        · exact Or.inr (Or.inl h)
      · rcases F0 with h | h
        · exact Or.inl (e01 h h1)
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (rowz2 hb2))
      · exact Or.inl e10
      · exact Or.inl (e11 h1)
      · exact Or.inr (Or.inr (rowz2 hb2))
      · exact Or.inl e20
      · exact Or.inl e21
      · exact Or.inr (Or.inr (rowz2 hb2))
    · have hb1 : B 1 1 = 0 := by
        rcases diag_cases hA hB hrel 1 with h | h
        · exact absurd h h1
        · exact h.2
      fin_cases p <;> fin_cases q
      · rcases F0 with h | h
        · exact Or.inl (e00 h)
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (rowz1 hb1 hb2))
      · exact Or.inr (Or.inr (rowz2 hb2))
      · exact Or.inl e10
      · exact Or.inr (Or.inr (rowz1 hb1 hb2))
      · exact Or.inr (Or.inr (rowz2 hb2))
      · exact Or.inl e20
      · exact Or.inr (Or.inr (rowz1 hb1 hb2))
      · exact Or.inr (Or.inr (rowz2 hb2))

end Lower

end M5UT
```

### `M5MainCase.lean`

```lean
import M5Lower3
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The main case of the lower bound in dimension 3

Here `a₀ = 0`, `a₁ = e ≠ 0`, `a₂ ∈ {−∞, 0}`, `b₀ = c₀ = p`, `b₁ = c₁ = −∞`, `b₂ = r`
(integers `e, p, r`).  Then `A^(β+2) = e^β K + L` with `K, L` independent of `β`, all entries
of `(BA)^(α+1) A^(β+2) B^(γ+1)` except `(0,2)` depend only on `α + γ`, and the `(0,2)` entry
is `(αp + βe + γr) ⊗ K* ⊕ G(α, γ)`.  The collision lemma finishes.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

theorem zb_lin (α β γ : ℕ) (p e r : ℤ) :
    zb (α * p + β * e + γ * r) = zb p ^ α * zb e ^ β * zb r ^ γ := by
  rw [zb_pow, zb_pow, zb_pow, zb_mul_zb, zb_mul_zb]

theorem main_case {A B : Matrix (Fin 3) (Fin 3) Zbar} (hA : A ∈ UT 3) (hB : B ∈ UT 3)
    (e p r : ℤ) (he : e ≠ 0) (ha0 : A 0 0 = 1) (ha1 : A 1 1 = zb e) (ha2 : Idem (A 2 2))
    (hb0 : B 0 0 = zb p) (hb1 : B 1 1 = 0) (hb2 : B 2 2 = zb r) :
    ∃ α β γ α' β' γ' : ℕ, (α, β, γ) ≠ (α', β', γ') ∧
      X3 A B (α + 1) (β + 1) (γ + 1) = X3 A B (α' + 1) (β' + 1) (γ' + 1) := by
  have hC := (UT 3).mul_mem hB hA
  have hc0 : (B * A) 0 0 = zb p := by rw [diag_mul3 hB hA, hb0, ha0, mul_one]
  have hc1 : (B * A) 1 1 = 0 := by rw [diag_mul3 hB hA, hb1, zero_mul]
  have hc2 : (B * A) 2 2 = zb r * A 2 2 := by rw [diag_mul3 hB hA, hb2]
  obtain ⟨C, hCdef⟩ : ∃ C, C = B * A := ⟨_, rfl⟩
  rw [← hCdef] at hC hc0 hc1 hc2
  have hX3 : ∀ α β γ, X3 A B α β γ = C ^ α * A ^ β * B ^ γ := by
    intro α β γ; rw [X3, hCdef]
  obtain ⟨κ, l, hκ⟩ := one_add_zb_pow e
  obtain ⟨κ', l', hκ'⟩ := zb_add_idem_pow e ha2
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin 3) (Fin 3) Zbar, K =
      !![0, A 0 1 * zb e * κ, A 0 1 * A 1 2 * κ;
         0, zb e ^ 2, A 1 2 * zb e * κ';
         0, 0, 0] := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin 3) (Fin 3) Zbar, L =
      !![1, A 0 1 * l, A 0 2 + A 0 1 * A 1 2 * l;
         0, 0, A 1 2 * l';
         0, 0, A 2 2] := ⟨_, rfl⟩
  have hdec : ∀ β : ℕ, A ^ (β + 2) = zb e ^ β • K + L := by
    intro β
    obtain ⟨a00, a11, a22, a01, a12, a02⟩ := pow3 hA (β + 1)
    have hP := pow_mem_UT hA (β + 1 + 1)
    have h10 := UT3_10 hP
    have h20 := UT3_20 hP
    have h21 := UT3_21 hP
    show A ^ (β + 1 + 1) = _
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hK, hL, a00, ha0]
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      simp [hK, hL, a01, ha0, ha1, hκ]
      ring
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      simp [hK, hL, a02, ha0, ha1, ha2.one_add]
      simp only [corner]
      rw [add_right_comm 1 (zb e), ha2.one_add, hκ]
      ring
    · simp [hK, hL, h10]
    · simp [hK, hL, a11, ha1]
      ring
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      simp [hK, hL, a12, ha1, hκ']
      ring
    · simp [hK, hL, h20]
    · simp [hK, hL, h21]
    · simp [hK, hL, a22, ha2.pow_succ]
  have hsplit : ∀ α β γ : ℕ, X3 A B (α + 1) (β + 2) (γ + 1) =
      zb e ^ β • (C ^ (α + 1) * K * B ^ (γ + 1)) + C ^ (α + 1) * L * B ^ (γ + 1) := by
    intro α β γ
    rw [hX3, hdec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine collide (X3 A B) e p r he
    (zb p * (A 0 1 * zb e * κ * B 1 2 + A 0 1 * A 1 2 * κ * zb r) +
      C 0 1 * (zb e ^ 2 * B 1 2 + A 1 2 * zb e * κ' * zb r))
    (fun i j s => (!![zb p ^ (s + 2), B 0 1 * zb p ^ (s + 1), 0;
        0, 0, C 1 2 * A 2 2 * zb r ^ (s + 1);
        0, 0, A 2 2 * zb r ^ (s + 2)] : Matrix (Fin 3) (Fin 3) Zbar) i j)
    (fun α γ => (C ^ (α + 1) * L * B ^ (γ + 1)) 0 2) ?_
  intro α β γ
  obtain ⟨c00, c11, c22, c01, c12, -⟩ := pow3 hC α
  obtain ⟨d00, d11, d22, d01, d12, -⟩ := pow3 hB γ
  have lc := pow_mem_UT hC (α + 1)
  have lb := pow_mem_UT hB (γ + 1)
  have c10 := UT3_10 lc
  have c20 := UT3_20 lc
  have c21 := UT3_21 lc
  have d10 := UT3_10 lb
  have d20 := UT3_20 lb
  have d21 := UT3_21 lb
  rw [hc0] at c00
  rw [hc1, zero_pow (Nat.succ_ne_zero α)] at c11
  rw [hc2] at c22
  rw [hc0, hc1, add_zero] at c01
  rw [hc1, zero_add, hc2] at c12
  rw [hb0] at d00
  rw [hb1, zero_pow (Nat.succ_ne_zero γ)] at d11
  rw [hb2] at d22
  rw [hb0, hb1, add_zero] at d01
  rw [hb1, zero_add, hb2] at d12
  constructor
  · intro i j hij
    rw [hsplit]
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hK, hL, c00, c11, c22, c01, c12, c10, c20, c21,
        d00, d11, d22, d01, d12, d10, d20, d21]
    · ring
    · ring
    · rcases ha2 with h2 | h2
      · simp [h2]
      · simp [h2]; ring
    · rcases ha2 with h2 | h2
      · simp [h2]
      · simp [h2]; ring
  · rw [hsplit, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
    rw [zb_lin]
    simp [Matrix.mul_apply, Fin.sum_univ_three, hK, c00, c11, c01, c10, c20, c21,
      d22, d12, d10, d20, d21]
    ring

end M5UT
```

### `M5Main.lean`

```lean
import M5MainCase
import Mathlib.Tactic.IntervalCases

/-!
# MathDB 356232: `M5 = Mon⟨a, b | aba = ba⟩` has UT-rank exactly 4

Conjecture 2.11 of C.-F. Nyberg-Brodda, *Tropical one-relation monoids*, arXiv:2209.12612.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace M5UT

section Lower

variable {A B : Matrix (Fin 3) (Fin 3) Zbar}

/-- For `A, B ∈ UT₃(ℤ̄)` with `ABA = BA`, two distinct normal forms (all exponents `≥ 1`)
have the same image. -/
theorem lower3 (hA : A ∈ UT 3) (hB : B ∈ UT 3) (hrel : A * B * A = B * A) :
    ∃ α β γ α' β' γ' : ℕ, (α, β, γ) ≠ (α', β', γ') ∧
      X3 A B (α + 1) (β + 1) (γ + 1) = X3 A B (α' + 1) (β' + 1) (γ' + 1) := by
  by_cases hm : Idem (A 1 1) ∨ (B * A) 0 0 = 0 ∨ B 2 2 = 0
  · exact ⟨2, 2, 2, 2, 3, 2, by simp, invariant_case hA hB hrel hm⟩
  · simp only [not_or] at hm
    obtain ⟨h1, hc0, hb2⟩ := hm
    obtain ⟨e, he, hae⟩ := not_idem h1
    have hb1 : B 1 1 = 0 := ((diag_cases hA hB hrel 1).resolve_left h1).2
    have ha0 := diag_one hA hB hrel 0 hc0
    have hc0' : (B * A) 0 0 = B 0 0 := by rw [diag_mul3 hB hA, ha0, mul_one]
    obtain ⟨p, hp⟩ : ∃ p, B 0 0 = zb p := by
      rcases cases_zb' (B 0 0) with h | h
      · exact absurd (hc0'.trans h) hc0
      · exact h
    obtain ⟨r, hr⟩ : ∃ r, B 2 2 = zb r := by
      rcases cases_zb' (B 2 2) with h | h
      · exact absurd h hb2
      · exact h
    have ha2 : Idem (A 2 2) := (diag_cases hA hB hrel 2).resolve_right (fun h => hb2 h.2)
    exact main_case hA hB e p r he ha0 hae ha2 hp hb1 hr

end Lower

/-- `M5` does not embed in `UT₃(ℤ̄)`. -/
theorem not_UTEmbeds_three : ¬ UTEmbeds 3 := by
  rintro ⟨f, hf⟩
  obtain ⟨α, β, γ, α', β', γ', hne, heq⟩ :=
    lower3 (f ga).2 (f gb).2 (hom_rel f)
  have hfe : f (N (α + 1) (β + 1) (γ + 1)) = f (N (α' + 1) (β' + 1) (γ' + 1)) := by
    apply Subtype.ext
    rw [hom_N, hom_N]
    exact heq
  have h := N_injective (hf hfe)
  simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact hne rfl

/-! ## Padding `UTₙ` into `UT₃` for `n ≤ 2` -/

/-- Block padding `X ↦ diag(X, −∞)`. -/
def padM {n : ℕ} (M : Matrix (Fin n) (Fin n) Zbar) : Matrix (Fin 3) (Fin 3) Zbar :=
  fun i j => if h : i.val < n ∧ j.val < n then M ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

theorem padM_mul {n : ℕ} (hn : n ≤ 2) (M P : Matrix (Fin n) (Fin n) Zbar) :
    padM (M * P) = padM M * padM P := by
  interval_cases n <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [padM, Matrix.mul_apply, Fin.sum_univ_succ]

theorem padM_injective {n : ℕ} (hn : n ≤ 2) : Function.Injective (padM (n := n)) := by
  intro M P h
  ext i j
  have := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  simpa [padM] using this

theorem padM_mem {n : ℕ} {M : Matrix (Fin n) (Fin n) Zbar} (hM : M ∈ UT n) : padM M ∈ UT 3 := by
  intro i j hij
  simp only [padM]
  split_ifs with h
  · exact hM _ _ (Fin.mk_lt_mk.2 hij)
  · rfl

/-- The padding as a semigroup homomorphism `UTₙ → UT₃`. -/
def padHom {n : ℕ} (hn : n ≤ 2) : UT n →ₙ* UT 3 where
  toFun M := ⟨padM M.1, padM_mem M.2⟩
  map_mul' M P := Subtype.ext (padM_mul hn M.1 P.1)

theorem padHom_injective {n : ℕ} (hn : n ≤ 2) : Function.Injective (padHom hn) := by
  intro M P h
  exact Subtype.ext (padM_injective hn (congrArg Subtype.val h))

theorem not_UTEmbeds_le_three : ∀ n ≤ 3, ¬ UTEmbeds n := by
  intro n hn ⟨f, hf⟩
  rcases Nat.lt_or_ge n 3 with h | h
  · exact not_UTEmbeds_three ⟨(padHom (by omega : n ≤ 2)).comp f,
      (padHom_injective (by omega)).comp hf⟩
  · obtain rfl : n = 3 := by omega
    exact not_UTEmbeds_three ⟨f, hf⟩

/-! ## The endpoint -/

/-- **Conjecture 2.11** (Nyberg-Brodda): `M5` has UT-rank exactly 4. -/
theorem conjecture_2_11 : Conjecture_2_11 := ⟨UTEmbeds_four, not_UTEmbeds_le_three⟩

/-- MathDB 356232, unfolded: `M5` embeds as a semigroup in `UT₄(ℤ̄)` and in no `UTₙ(ℤ̄)`
with `n ≤ 3`. -/
theorem mathdb356232 :
    (∃ f : M5 →ₙ* UT 4, Function.Injective f) ∧
      ∀ n ≤ 3, ¬ ∃ f : M5 →ₙ* UT n, Function.Injective f :=
  conjecture_2_11

/-! ## Non-vacuity checks -/

/-- The embedding is induced by the corrected matrices: `f4 a = A4`, `f4 b = B4`. -/
theorem f4_gens : ((f4 ga : UT 4) : Matrix (Fin 4) (Fin 4) Zbar) = A4 ∧
    ((f4 gb : UT 4) : Matrix (Fin 4) (Fin 4) Zbar) = B4 := ⟨rfl, rfl⟩

/-- The corrected matrices satisfy the defining relation. -/
theorem rel_holds : A4 * B4 * A4 = B4 * A4 := A4_B4_rel

/-- The embedding even sends the empty word to the identity matrix. -/
theorem f4_one : ((f4 1 : UT 4) : Matrix (Fin 4) (Fin 4) Zbar) = 1 := map_one psi4

/-- `M5` is infinite (so injectivity is a real constraint). -/
theorem M5_infinite : Function.Injective (fun k : ℕ => N 0 k 0) := by
  intro k k' h
  have := N_injective h
  simpa using this

end M5UT
```

### `M5Printed.lean`

```lean
import M5Main

/-!
# The matrix printed in the source is not an embedding

With the printed value `B₁₁ = 1` (source Lemma 2.9), the relation `ABA = BA` still holds,
but `(ba)b²` and `(ba)²b` (distinct normal forms `N 1 0 2 ≠ N 2 0 1`) have equal images.
This supplementary check justifies the correction `B₁₁ = −1` used in `B4`.
-/

set_option linter.unusedSimpArgs false

namespace M5UT

/-- The matrix `B` as printed in arXiv:2209.12612, Lemma 2.9 (`B₁₁ = 1`). -/
def B4printed : Matrix (Fin 4) (Fin 4) Zbar :=
  !![zb 1, zb 0, zb 0, zb (-1);
     0, 0, 0, zb 0;
     0, 0, zb 0, 0;
     0, 0, 0, zb 1]

theorem printed_rel : A4 * B4printed * A4 = B4printed * A4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A4, B4printed, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]

theorem printed_collision :
    (B4printed * A4) * B4printed ^ 2 = (B4printed * A4) ^ 2 * B4printed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A4, B4printed, pow_two, Matrix.mul_apply, Fin.sum_univ_four, zb_mul_zb, zb_add_zb]

theorem printed_distinct : N 1 0 2 ≠ N 2 0 1 := by
  intro h
  have := N_injective h
  simp at this

end M5UT
```

### `M5Axioms.lean`

```lean
import M5Main
import M5Printed

/-! Endpoint statements, definitions and axiom reports. -/

open M5UT

#check @M5UT.mathdb356232
#check (M5UT.mathdb356232 :
  (∃ f : M5UT.M5 →ₙ* M5UT.UT 4, Function.Injective f) ∧
    ∀ n ≤ 3, ¬ ∃ f : M5UT.M5 →ₙ* M5UT.UT n, Function.Injective f)
#check @M5UT.conjecture_2_11
#print M5UT.Conjecture_2_11
#print M5UT.UTEmbeds
#print M5UT.M5
#print M5UT.rel5
#print M5UT.UT
#print M5UT.Zbar
#print M5UT.zb
#check @M5UT.zb_add_zb
#check @M5UT.zb_mul_zb
#check @M5UT.zero_eq_negInf
#check @M5UT.one_eq_zb_zero
#check @M5UT.negInf_add
#check @M5UT.negInf_mul
#check @M5UT.cases_zb
#check @M5UT.zb_injective
#check @M5UT.zb_ne_negInf
#print M5UT.A4
#print M5UT.B4
#check @M5UT.rel_holds
#check @M5UT.f4_gens
#check @M5UT.f4_one
#check @M5UT.M5_infinite
#check @M5UT.printed_rel
#check @M5UT.printed_collision
#check @M5UT.printed_distinct

#print axioms M5UT.mathdb356232
#print axioms M5UT.conjecture_2_11
#print axioms M5UT.UTEmbeds_four
#print axioms M5UT.not_UTEmbeds_le_three
#print axioms M5UT.zb_add_zb
#print axioms M5UT.zb_mul_zb
#print axioms M5UT.zero_eq_negInf
#print axioms M5UT.one_eq_zb_zero
#print axioms M5UT.negInf_add
#print axioms M5UT.negInf_mul
#print axioms M5UT.cases_zb
#print axioms M5UT.zb_injective
#print axioms M5UT.zb_ne_negInf
#print axioms M5UT.rel_holds
#print axioms M5UT.f4_gens
#print axioms M5UT.f4_one
#print axioms M5UT.M5_infinite
#print axioms M5UT.printed_rel
#print axioms M5UT.printed_collision
#print axioms M5UT.printed_distinct
```

