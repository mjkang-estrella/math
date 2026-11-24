# Lean source appendix — MathDB 335487

Modules are listed in import order; each block is byte-identical to `src/<Module>.lean`.

### `BinStatement.lean`

```lean
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# MathDB 335487: the statement (Gawron, Miska, Ulas, Conjecture 5.3)

Source (arXiv:1703.01955, Section 4): `b(n)` is the binary partition function, the number of
representations `n = ∑ εᵢ 2ⁱ` with `εᵢ ∈ ℕ`, i.e. the number of partitions of `n` into powers
of `2`; `b_m(n) := f_n(-m)` is the coefficient of `xⁿ` in `∏_{n ≥ 0} (1 - x^{2ⁿ})^{-m}`, and
"it is clear that `b_m(n)` is the convolution of `m` copies of the sequence `(b(n))`".

We define `bin n` literally as the number of partitions of `n` all of whose parts are powers
of `2`, and `b m` as the `m`-fold convolution of `bin` (with `b 0` the unit sequence).
-/

namespace MathDB335487

/-- Decidability of "`i` is a power of two" (any instance gives the same `bin`). -/
instance decPow2 (i : ℕ) : Decidable (∃ k, i = 2 ^ k) :=
  decidable_of_iff (∃ k < i + 1, i = 2 ^ k)
    ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, by
      subst hk; have := Nat.lt_two_pow_self (n := k); omega, hk⟩⟩

/-- The binary partition function: the number of partitions of `n` into powers of `2`. -/
def bin (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => ∀ i ∈ p.parts, ∃ k, i = 2 ^ k)).card

/-- `b m n = b_m(n)`: the `m`-fold convolution of the binary partition function
(the number of binary partitions of `n` with each part coloured in one of `m` colours). -/
def b : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => ∑ ij ∈ Finset.antidiagonal n, bin ij.1 * b m ij.2

/-- Conjecture 5.3 of Gawron–Miska–Ulas, as printed: for every `m ≥ 2` not of the form
`2^k - 1` with `k ∈ ℕ₊`, the sequence `(ν₂(b_m(n)))_{n ∈ ℕ}` is unbounded. -/
def Conjecture53 : Prop :=
  ∀ m : ℕ, 2 ≤ m → (∀ k : ℕ, 0 < k → m ≠ 2 ^ k - 1) →
    ∀ B : ℕ, ∃ n : ℕ, B < padicValNat 2 (b m n)

end MathDB335487
```

### `BinBridge.lean`

```lean
import BinStatement
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-!
# The binary partition recurrence, from the combinatorial definition

`bin (n+1) = bin n + (if 2 ∣ n+1 then bin ((n+1)/2) else 0)` and `bin 0 = 1`.
Partitions of `n+1` into powers of two that contain a part `1` correspond to those of `n`
(remove one `1`); those without a part `1` have only even parts, so they exist only when
`n+1` is even and then correspond to binary partitions of `(n+1)/2` (halve every part).
-/

namespace MathDB335487

open Multiset

/-- The finset of binary partitions of `n`. -/
abbrev BinP (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ i ∈ p.parts, ∃ k, i = 2 ^ k)

theorem bin_eq_card (n : ℕ) : bin n = (BinP n).card := rfl

/-- Add a part `1`. -/
def addOne {n : ℕ} (p : Nat.Partition n) : Nat.Partition (n + 1) where
  parts := 1 ::ₘ p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.1 hi with h | h
    · omega
    · exact p.parts_pos h
  parts_sum := by rw [Multiset.sum_cons, p.parts_sum]; omega

/-- Remove one part `1`. -/
def delOne {n : ℕ} (p : Nat.Partition (n + 1)) (h : 1 ∈ p.parts) : Nat.Partition n where
  parts := p.parts.erase 1
  parts_pos := fun hi => p.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have := Multiset.sum_erase h
    rw [p.parts_sum] at this
    omega

theorem card_with_one (n : ℕ) :
    ((BinP (n + 1)).filter (fun p => 1 ∈ p.parts)).card = (BinP n).card := by
  refine Finset.card_bij' (fun p hp => delOne p (Finset.mem_filter.1 hp).2)
    (fun q _ => addOne q) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro i hi
    exact hp.1 i (Multiset.mem_of_mem_erase hi)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨?_, Multiset.mem_cons_self _ _⟩
    intro i hi
    rcases Multiset.mem_cons.1 hi with h | h
    · exact ⟨0, by simp [h]⟩
    · exact hq i h
  · intro p hp
    exact Nat.Partition.ext (Multiset.cons_erase (Finset.mem_filter.1 hp).2)
  · intro q _
    exact Nat.Partition.ext (Multiset.erase_cons_head 1 q.parts)

theorem even_of_pow_ne_one {i : ℕ} (h1 : i ≠ 1) (h : ∃ k, i = 2 ^ k) : 2 ∣ i := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => simp at h1
  | succ k => exact ⟨2 ^ k, by ring⟩

/-- Double every part. -/
def dbl {n : ℕ} (p : Nat.Partition n) : Nat.Partition (2 * n) where
  parts := p.parts.map (fun i => 2 * i)
  parts_pos := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
    have := p.parts_pos hj
    omega
  parts_sum := by rw [Multiset.sum_map_mul_left, Multiset.map_id', p.parts_sum]

/-- Halve every part of a partition with only even parts. -/
def hlf {n : ℕ} (p : Nat.Partition (2 * n)) (h : ∀ i ∈ p.parts, 2 ∣ i) : Nat.Partition n where
  parts := p.parts.map (fun i => i / 2)
  parts_pos := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
    have h1 := p.parts_pos hj
    obtain ⟨c, rfl⟩ := h j hj
    omega
  parts_sum := by
    have h2 : (p.parts.map (fun i => 2 * (i / 2))).sum = p.parts.sum := by
      rw [Multiset.map_congr rfl (fun i hi => Nat.mul_div_cancel' (h i hi)), Multiset.map_id']
    rw [Multiset.sum_map_mul_left, p.parts_sum] at h2
    omega

theorem card_without_one (n : ℕ) :
    ((BinP (2 * n)).filter (fun p => ¬ 1 ∈ p.parts)).card = (BinP n).card := by
  have hev : ∀ p ∈ (BinP (2 * n)).filter (fun p => ¬ 1 ∈ p.parts), ∀ i ∈ p.parts, 2 ∣ i := by
    intro p hp i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact even_of_pow_ne_one (fun h => hp.2 (h ▸ hi)) (hp.1 i hi)
  refine Finset.card_bij' (fun p hp => hlf p (hev p hp)) (fun q _ => dbl q) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp' ⊢
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
    obtain ⟨k, hk⟩ := hp'.1 j hj
    cases k with
    | zero => exact absurd (hk ▸ hj) (by simpa using hp'.2)
    | succ k => exact ⟨k, by rw [hk, pow_succ]; omega⟩
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
      obtain ⟨k, rfl⟩ := hq j hj
      exact ⟨k + 1, by rw [pow_succ]; ring⟩
    · intro hi
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.1 hi
      omega
  · intro p hp
    apply Nat.Partition.ext
    change Multiset.map (fun i => 2 * i) (Multiset.map (fun i => i / 2) p.parts) = p.parts
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' p.parts]
    exact Multiset.map_congr rfl (fun i hi => Nat.mul_div_cancel' (hev p hp i hi))
  · intro q _
    apply Nat.Partition.ext
    change Multiset.map (fun i => i / 2) (Multiset.map (fun i => 2 * i) q.parts) = q.parts
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' q.parts]
    exact Multiset.map_congr rfl (fun i _ => by simp)

theorem card_without_one_odd (N : ℕ) (hN : ¬ 2 ∣ N) :
    ((BinP N).filter (fun p => ¬ 1 ∈ p.parts)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  apply hN
  rw [← p.parts_sum]
  exact Multiset.dvd_sum (fun i hi => even_of_pow_ne_one (fun h => h1 (h ▸ hi)) (hp i hi))

theorem bin_succ (n : ℕ) :
    bin (n + 1) = bin n + (if 2 ∣ n + 1 then bin ((n + 1) / 2) else 0) := by
  rw [bin_eq_card, ← Finset.card_filter_add_card_filter_not (s := BinP (n + 1))
    (fun p => 1 ∈ p.parts), card_with_one, ← bin_eq_card]
  congr 1
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    have key : ∀ N, N = 2 * k →
        ((BinP N).filter (fun p => ¬ 1 ∈ p.parts)).card = bin k := by
      rintro N rfl; exact card_without_one k
    rw [key (n + 1) hk, hk, Nat.mul_div_cancel_left k (by norm_num)]
  · exact card_without_one_odd (n + 1) h

theorem bin_zero : bin 0 = 1 := by
  rw [bin_eq_card, BinP, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_unique]
  intro p _ i hi
  have h1 := p.parts_pos hi
  have h2 := Nat.Partition.le_of_mem_parts hi
  omega

end MathDB335487
```

### `BinSeries.lean`

```lean
import BinBridge
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Data.ZMod.Basic

/-!
# Power series over `ZMod 32`

`H₁ = ∑ bin n xⁿ`, the Thue–Morse series `T = ∑ tₙ xⁿ`, the functional equations
`(1 - x) H₁(x) = H₁(x²)` and `T(x) = (1 - x) T(x²)`, the identity `T · H₁ = 1`,
`(T (1 - x))¹⁶ = 1` (mod 32), the key congruence
`H₁^m = (1 - x)^N T^(N - m)` for `16 ∣ N`, `m ≤ N` (all in `(ZMod 32)⟦X⟧`),
and `coeff n (H₁^m) = b m n`.
-/

namespace MathDB335487

open PowerSeries

abbrev R32 := ZMod 32

/-- `D2 F = F(x²)`. -/
noncomputable abbrev D2 : R32⟦X⟧ →ₐ[R32] R32⟦X⟧ := PowerSeries.expand 2 two_ne_zero

theorem coeff_D2_even (F : R32⟦X⟧) (n : ℕ) : coeff (2 * n) (D2 F) = coeff n F :=
  coeff_expand_mul 2 two_ne_zero F n

theorem coeff_D2_odd (F : R32⟦X⟧) (n : ℕ) : coeff (2 * n + 1) (D2 F) = 0 :=
  coeff_expand_of_not_dvd 2 two_ne_zero F (by omega)

theorem coeff_XD2_even (F : R32⟦X⟧) (n : ℕ) : coeff (2 * n) (X * D2 F) = 0 := by
  cases n with
  | zero => simp
  | succ n => rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, coeff_succ_X_mul, coeff_D2_odd]

theorem coeff_XD2_odd (F : R32⟦X⟧) (n : ℕ) : coeff (2 * n + 1) (X * D2 F) = coeff n F := by
  rw [coeff_succ_X_mul, coeff_D2_even]

theorem coeff_sect0 (F G : R32⟦X⟧) (n : ℕ) : coeff (2 * n) (D2 F + X * D2 G) = coeff n F := by
  rw [map_add, coeff_D2_even, coeff_XD2_even, add_zero]

theorem coeff_sect1 (F G : R32⟦X⟧) (n : ℕ) :
    coeff (2 * n + 1) (D2 F + X * D2 G) = coeff n G := by
  rw [map_add, coeff_D2_odd, coeff_XD2_odd, zero_add]

theorem D2_one_sub_X : D2 (1 - X) = 1 - X ^ 2 := by
  rw [map_sub, map_one, expand_X]

theorem coeff_one_sub_X_mul_zero (F : R32⟦X⟧) : coeff 0 ((1 - X) * F) = coeff 0 F := by
  rw [sub_mul, one_mul, map_sub, coeff_zero_X_mul, sub_zero]

theorem coeff_one_sub_X_mul_succ (F : R32⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 - X) * F) = coeff (n + 1) F - coeff n F := by
  rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]

/-! ## Thue–Morse -/

/-- The Prouhet–Thue–Morse sequence `tₙ = (-1)^{s₂(n)}`, via `t₀ = 1`, `t₂ₙ = tₙ`, `t₂ₙ₊₁ = -tₙ`. -/
def tm : ℕ → ℤ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 0 then tm ((n + 1) / 2) else - tm ((n + 1) / 2)
decreasing_by all_goals omega

theorem tm_zero : tm 0 = 1 := by rw [tm]

theorem tm_even (n : ℕ) : tm (2 * n) = tm n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, tm]
    rw [ite_eq_left (by omega), show (2 * n + 1 + 1) / 2 = n + 1 by omega]

theorem tm_odd (n : ℕ) : tm (2 * n + 1) = - tm n := by
  rw [tm, ite_eq_right (by omega), show (2 * n + 1) / 2 = n by omega]

theorem tm_pm (n : ℕ) : tm n = 1 ∨ tm n = -1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · cases j with
      | zero => left; rw [Nat.mul_zero, tm_zero]
      | succ j => rw [tm_even]; exact ih _ (by omega)
    · rw [tm_odd]
      rcases ih j (by omega) with h | h <;> rw [h] <;> simp

/-- The Thue–Morse series `T(x) = ∏ (1 - x^{2^i})`, over `ZMod 32`, by its coefficients. -/
noncomputable def T : R32⟦X⟧ := mk fun n => (tm n : R32)

/-- `H₁ = ∑ bin n xⁿ` over `ZMod 32`. -/
noncomputable def H1 : R32⟦X⟧ := mk fun n => (bin n : R32)

theorem T_func : T = (1 - X) * D2 T := by
  ext n
  cases n with
  | zero => rw [coeff_one_sub_X_mul_zero, show (0 : ℕ) = 2 * 0 from rfl, coeff_D2_even]
  | succ k =>
    rw [coeff_one_sub_X_mul_succ]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [coeff_D2_odd, coeff_D2_even, T, coeff_mk, coeff_mk, tm_odd]; push_cast; ring
    · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, coeff_D2_odd, coeff_D2_even, T, coeff_mk,
        coeff_mk, tm_even, sub_zero]

theorem H1_func : (1 - X) * H1 = D2 H1 := by
  ext n
  cases n with
  | zero => rw [coeff_one_sub_X_mul_zero, show (0 : ℕ) = 2 * 0 from rfl, coeff_D2_even]
  | succ k =>
    rw [coeff_one_sub_X_mul_succ, coeff_expand, H1, coeff_mk, coeff_mk, bin_succ]
    push_cast
    split_ifs <;> simp [coeff_mk]

theorem coeff_zero_T : coeff 0 T = 1 := by rw [T, coeff_mk, tm_zero]; simp

theorem coeff_zero_mul (F G : R32⟦X⟧) : coeff 0 (F * G) = coeff 0 F * coeff 0 G := by
  rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

theorem T_mul_H1 : T * H1 = 1 := by
  have hG : T * H1 = D2 (T * H1) := by
    calc T * H1 = (1 - X) * D2 T * H1 := by conv_lhs => rw [T_func]
      _ = D2 T * ((1 - X) * H1) := by ring
      _ = D2 (T * H1) := by rw [H1_func, map_mul]
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [coeff_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_mul, coeff_zero_T, H1, coeff_mk, bin_zero]; simp
    · rw [ite_eq_right (by omega), hG, coeff_expand]
      split_ifs with h
      · rw [ih (n / 2) (by omega), coeff_one, ite_eq_right (by omega)]
      · rfl

/-! ## The congruence `H₁^m ≡ (1 - x)^N T^{N-m}` mod 32 -/

theorem pow16 {A : Type*} [CommRing A] (h : (32 : A) = 0) (B W : A) :
    (B + 2 * W) ^ 16 = B ^ 16 := by
  have e1 : (B + 2 * W) ^ 2 = B ^ 2 + 4 * (B * W + W ^ 2) := by ring
  have e2 : ∀ V : A, (B ^ 2 + 4 * V) ^ 2 = B ^ 4 + 8 * (B ^ 2 * V + 2 * V ^ 2) := by
    intro V; ring
  have e3 : ∀ V : A, (B ^ 4 + 8 * V) ^ 2 = B ^ 8 + 16 * (B ^ 4 * V + 4 * V ^ 2) := by
    intro V; ring
  have e4 : ∀ V : A, (B ^ 8 + 16 * V) ^ 2 = B ^ 16 + 32 * (B ^ 8 * V + 8 * V ^ 2) := by
    intro V; ring
  calc (B + 2 * W) ^ 16 = ((((B + 2 * W) ^ 2) ^ 2) ^ 2) ^ 2 := by ring
    _ = B ^ 16 := by rw [e1, e2, e3, e4, h, zero_mul, add_zero]

theorem h32 : (32 : R32⟦X⟧) = 0 := by
  have : (32 : R32) = 0 := by decide
  calc (32 : R32⟦X⟧) = C (32 : R32) := (map_ofNat C 32).symm
    _ = 0 := by rw [this, map_zero]

/-- `T (1 - x) = 1 + 2U`. -/
noncomputable def U : R32⟦X⟧ :=
  mk fun n => if n = 0 then 0 else if tm n = tm (n - 1) then 0 else (tm n : R32)

theorem T_one_sub_X : T * (1 - X) = 1 + 2 * U := by
  rw [mul_comm]
  ext n
  cases n with
  | zero =>
    rw [coeff_one_sub_X_mul_zero, coeff_zero_T, map_add, coeff_one, U,
      show (2 : R32⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_mk]
    simp
  | succ k =>
    rw [coeff_one_sub_X_mul_succ, map_add, coeff_one, U,
      show (2 : R32⟦X⟧) = C 2 from (map_ofNat C 2).symm, coeff_C_mul, coeff_mk, T, coeff_mk,
      coeff_mk, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
    split_ifs with h
    · rw [h]; simp
    · have hk : tm k = - tm (k + 1) := by
        rcases tm_pm k with h1 | h1 <;> rcases tm_pm (k + 1) with h2 | h2 <;>
          rw [h1, h2] at h ⊢ <;> simp_all
      rw [hk]; push_cast; ring

theorem T_one_sub_X_pow16 : (T * (1 - X)) ^ 16 = 1 := by
  rw [T_one_sub_X, pow16 h32, one_pow]

/-- The key congruence (★): `H₁^m = (1 - x)^N T^{N-m}` in `(ZMod 32)⟦X⟧` for `16 ∣ N`, `m ≤ N`. -/
theorem star (m N : ℕ) (hmN : m ≤ N) (h16 : 16 ∣ N) : H1 ^ m = (1 - X) ^ N * T ^ (N - m) := by
  obtain ⟨c, rfl⟩ := h16
  obtain ⟨r, hr⟩ : ∃ r, 16 * c = m + r := ⟨16 * c - m, by omega⟩
  rw [hr, Nat.add_sub_cancel_left]
  calc H1 ^ m = H1 ^ m * ((T * (1 - X)) ^ 16) ^ c := by rw [T_one_sub_X_pow16, one_pow, mul_one]
    _ = H1 ^ m * (T * (1 - X)) ^ (m + r) := by rw [← pow_mul, hr]
    _ = (T * H1) ^ m * ((1 - X) ^ (m + r) * T ^ r) := by
          generalize (1 - X : R32⟦X⟧) = Y; ring
    _ = (1 - X) ^ (m + r) * T ^ r := by rw [T_mul_H1, one_pow, one_mul]

theorem coeff_H1_pow (m n : ℕ) : coeff n (H1 ^ m) = (b m n : R32) := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, coeff_one, b]
    split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ', coeff_mul, b]
    push_cast
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    rw [ih, H1, coeff_mk]

/-- Collapsing powers of `1 - x` mod 32: `(1 - x)^{2^{a+4} c} = ((1 - x)^{16c})(x^{2^a})`. -/
theorem pw_dil (a c : ℕ) :
    ((1 : R32⟦X⟧) - X) ^ (2 ^ (a + 4) * c) = (⇑D2)^[a] ((1 - X) ^ (16 * c)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ← ih, map_pow, D2_one_sub_X]
    have e : ((1 : R32⟦X⟧) - X) ^ 2 = (1 - X ^ 2) + 2 * (X ^ 2 - X) := by ring
    calc ((1 : R32⟦X⟧) - X) ^ (2 ^ (a + 1 + 4) * c)
          = (((1 : R32⟦X⟧) - X) ^ 2) ^ (16 * (2 ^ a * c)) := by
            rw [← pow_mul]; congr 1; ring
      _ = ((1 - X ^ 2) ^ 16) ^ (2 ^ a * c) := by rw [e, pow_mul, pow16 h32]
      _ = (1 - X ^ 2) ^ (2 ^ (a + 4) * c) := by rw [← pow_mul]; congr 1; ring

end MathDB335487
```

### `BinAutomaton.lean`

```lean
import BinSeries

/-!
# Polynomials as lists, the section maps, and the automaton soundness lemma

A list `[a₀, a₁, …]` of naturals stands for `∑ aᵢ xⁱ ∈ (ZMod 32)⟦X⟧`.
`phi0 R l`, `phi1 R l` are the even and odd sections of `l · (1 - x)^R`. Since
`T^R = (1 - x)^R T^R(x²)`, the coefficient of `x^{2n+ε}` in `l · T^R` is the coefficient of
`xⁿ` in `phi_ε(l) · T^R`. A finite table closed under `phi0`, `phi1` whose entries all have
constant term `≢ 0 (mod 32)` therefore certifies that `l · T^R` has no coefficient `≡ 0`.
-/

namespace MathDB335487

open PowerSeries

/-- The power series of a coefficient list (constant term first), read mod 32. -/
noncomputable def toPS : List ℕ → R32⟦X⟧
  | [] => 0
  | a :: l => C (a : R32) + X * toPS l

def addL : List ℕ → List ℕ → List ℕ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, c :: m => (a + c) % 32 :: addL l m

def scal (c : ℕ) (l : List ℕ) : List ℕ := l.map (fun a => c * a % 32)

def mulL : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: l, p => addL (scal a p) (0 :: mulL l p)

/-- `sect true` takes the even-indexed coefficients, `sect false` the odd-indexed ones. -/
def sect : Bool → List ℕ → List ℕ
  | _, [] => []
  | true, a :: l => a :: sect false l
  | false, _ :: l => sect true l

/-- `(1 - x)^R` as a list (`31 ≡ -1`). -/
def pwL : ℕ → List ℕ
  | 0 => [1]
  | R + 1 => mulL (pwL R) [1, 31]

def phi0 (R : ℕ) (l : List ℕ) : List ℕ := sect true (mulL l (pwL R))
def phi1 (R : ℕ) (l : List ℕ) : List ℕ := sect false (mulL l (pwL R))

/-- Equality of the represented polynomials mod 32 (trailing zeros allowed). -/
def normEq : List ℕ → List ℕ → Bool
  | [], m => m.all (fun c => c % 32 == 0)
  | a :: l, [] => (a :: l).all (fun c => c % 32 == 0)
  | a :: l, c :: m => (a % 32 == c % 32) && normEq l m

theorem cast_mod32 (a : ℕ) : (((a % 32 : ℕ)) : R32) = (a : R32) := ZMod.natCast_mod a 32

theorem toPS_addL (l m : List ℕ) : toPS (addL l m) = toPS l + toPS m := by
  induction l generalizing m with
  | nil => simp [addL, toPS]
  | cons a l ih =>
    cases m with
    | nil => simp [addL, toPS]
    | cons c m => simp only [addL, toPS, ih, cast_mod32]; push_cast; rw [map_add]; ring

theorem toPS_scal (c : ℕ) (l : List ℕ) : toPS (scal c l) = C (c : R32) * toPS l := by
  induction l with
  | nil => simp [scal, toPS]
  | cons a l ih =>
    simp only [scal, List.map_cons, toPS] at ih ⊢
    rw [ih, cast_mod32]; push_cast; rw [map_mul]; ring

theorem toPS_mulL (l p : List ℕ) : toPS (mulL l p) = toPS l * toPS p := by
  induction l with
  | nil => simp [mulL, toPS]
  | cons a l ih =>
    rw [mulL, toPS_addL, toPS_scal, toPS, toPS, ih]; push_cast; rw [map_zero]; ring

theorem toPS_sect (l : List ℕ) :
    toPS l = D2 (toPS (sect true l)) + X * D2 (toPS (sect false l)) := by
  induction l with
  | nil => simp [sect, toPS]
  | cons a l ih =>
    rw [sect, sect, toPS, toPS, ih, map_add, map_mul, expand_C, expand_X]
    ring

theorem toPS_pwL (R : ℕ) : toPS (pwL R) = (1 - X) ^ R := by
  induction R with
  | zero => simp [pwL, toPS]
  | succ R ih =>
    rw [pwL, toPS_mulL, ih, pow_succ]
    congr 1
    have h31 : ((31 : ℕ) : R32) = -1 := by decide
    simp only [toPS, h31, Nat.cast_one, map_one, map_neg, mul_zero, add_zero]
    ring

theorem toPS_allZero (l : List ℕ) (h : l.all (fun c => c % 32 == 0) = true) : toPS l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [toPS, ih h.2, ← cast_mod32, h.1]; simp

theorem toPS_normEq (l m : List ℕ) (h : normEq l m = true) : toPS l = toPS m := by
  induction l generalizing m with
  | nil => rw [normEq] at h; rw [toPS_allZero m h]; rfl
  | cons a l ih =>
    cases m with
    | nil => rw [normEq] at h; rw [toPS_allZero _ h]; rfl
    | cons c m =>
      simp only [normEq, Bool.and_eq_true, beq_iff_eq] at h
      rw [toPS, toPS, ih m h.2, ← cast_mod32, h.1, cast_mod32]

theorem coeff_zero_toPS (l : List ℕ) : coeff 0 (toPS l) = ((l.headD 0 : ℕ) : R32) := by
  cases l with
  | nil => simp [toPS]
  | cons a l => simp [toPS]

/-! ## The section step -/

theorem split_mul (l : List ℕ) (R : ℕ) (F : R32⟦X⟧) :
    toPS l * (1 - X) ^ R * D2 F =
      D2 (toPS (phi0 R l) * F) + X * D2 (toPS (phi1 R l) * F) := by
  rw [← toPS_pwL, ← toPS_mulL, toPS_sect (mulL l (pwL R)), map_mul, map_mul, phi0, phi1]
  ring

theorem step0 (l : List ℕ) (R : ℕ) (F : R32⟦X⟧) (n : ℕ) :
    coeff (2 * n) (toPS l * (1 - X) ^ R * D2 F) = coeff n (toPS (phi0 R l) * F) := by
  rw [split_mul, coeff_sect0]

theorem step1 (l : List ℕ) (R : ℕ) (F : R32⟦X⟧) (n : ℕ) :
    coeff (2 * n + 1) (toPS l * (1 - X) ^ R * D2 F) = coeff n (toPS (phi1 R l) * F) := by
  rw [split_mul, coeff_sect1]

theorem T_pow_func (R : ℕ) : T ^ R = (1 - X) ^ R * D2 (T ^ R) := by
  conv_lhs => rw [T_func]
  rw [mul_pow, map_pow]

theorem mul_T_pow (l : List ℕ) (R : ℕ) :
    toPS l * T ^ R = toPS l * (1 - X) ^ R * D2 (T ^ R) := by
  conv_lhs => rw [T_pow_func]
  ring

/-- `l · D2(C) · T = l · (1 - x) · D2(C · T)`. -/
theorem mul_D2_T (l : List ℕ) (Cs : R32⟦X⟧) :
    toPS l * D2 Cs * T = toPS l * (1 - X) ^ 1 * D2 (Cs * T) := by
  conv_lhs => rw [T_func]
  rw [map_mul]; ring

theorem coeff_zero_T_pow (R : ℕ) : coeff 0 (T ^ R) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
    coeff_zero_T, one_pow]

theorem natCast_ne_zero_of_mod {a : ℕ} (h : a % 32 ≠ 0) : (a : R32) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; omega

/-! ## The automaton check and its soundness -/

/-- Row `i` of an automaton table: constant term `≢ 0 (mod 32)`, and both sections of the
entry are (mod 32) table entries at the recorded indices. -/
def rowOK (R : ℕ) (tbl : List (List ℕ)) (tr : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  ((tbl.getD i []).headD 0 % 32 != 0) &&
  decide ((tr.getD i (0, 0)).1 < tbl.length) && decide ((tr.getD i (0, 0)).2 < tbl.length) &&
  normEq (phi0 R (tbl.getD i [])) (tbl.getD (tr.getD i (0, 0)).1 []) &&
  normEq (phi1 R (tbl.getD i [])) (tbl.getD (tr.getD i (0, 0)).2 [])

/-- All rows of the table are correct. -/
def checkAut (R : ℕ) (tbl : List (List ℕ)) (tr : List (ℕ × ℕ)) : Bool :=
  (List.range tbl.length).all (rowOK R tbl tr)

theorem aut_sound_rows (R : ℕ) (tbl : List (List ℕ)) (tr : List (ℕ × ℕ))
    (h : ∀ i < tbl.length, rowOK R tbl tr i = true) :
    ∀ n, ∀ i < tbl.length, coeff n (toPS (tbl.getD i []) * T ^ R) ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi
    have hc := h i hi
    simp only [rowOK, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨h0, ha⟩, hb⟩, e0⟩, e1⟩ := hc
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_mul, coeff_zero_T_pow, mul_one, coeff_zero_toPS]
      exact natCast_ne_zero_of_mod h0
    · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
      · rw [mul_T_pow, step0, toPS_normEq _ _ e0]
        exact ih k (by omega) _ ha
      · rw [mul_T_pow, step1, toPS_normEq _ _ e1]
        exact ih k (by omega) _ hb

theorem aut_sound (R : ℕ) (tbl : List (List ℕ)) (tr : List (ℕ × ℕ))
    (h : checkAut R tbl tr = true) :
    ∀ n, ∀ i < tbl.length, coeff n (toPS (tbl.getD i []) * T ^ R) ≠ 0 :=
  aut_sound_rows R tbl tr (fun i hi => (List.all_eq_true.1 h) i (List.mem_range.2 hi))

end MathDB335487
```

### `BinData11.lean`

```lean
import BinAutomaton

/-! Certificate for `m = 11`: with `N = 16`, `R = 5`, `b₁₁ ≡ (1 - x)^16 T^5 (mod 32)`;
the 70 states reachable from `(1 - x)^16` under `phi0 5`, `phi1 5` (generated by
`scripts/automata.py`, checked here by kernel evaluation). -/

namespace MathDB335487

def tbl11 : List (List ℕ) := [
  [1, 16, 24, 16, 28, 16, 8, 16, 6, 16, 8, 16, 28, 16, 24, 16, 1],
  [1, 18, 1, 24, 2, 12, 10, 24, 29, 18, 21],
  [11, 14, 3, 8, 22, 20, 30, 8, 31, 14, 31],
  [1, 17, 5, 5, 3, 19, 23, 23],
  [13, 29, 1, 1, 7, 23, 11, 11],
  [11, 11, 23, 7, 1, 1, 29, 13],
  [23, 23, 19, 3, 5, 5, 17, 1],
  [1, 26, 23, 12, 31, 26, 9],
  [12, 12, 24, 24, 28, 28],
  [13, 18, 11, 28, 19, 18, 21],
  [28, 28, 24, 24, 12, 12],
  [11, 14, 13, 4, 21, 14, 19],
  [20, 20, 8, 8, 4, 4],
  [23, 6, 1, 20, 9, 6, 31],
  [4, 4, 8, 8, 20, 20],
  [1, 31, 10, 30, 5, 19],
  [21, 19, 18, 6, 9, 23],
  [12, 20, 24, 8, 28, 4],
  [16, 0, 0, 0, 16],
  [13, 19, 2, 6, 1, 23],
  [17, 23, 10, 14, 21, 11],
  [28, 4, 24, 8, 12, 20],
  [11, 21, 14, 10, 23, 17],
  [23, 1, 6, 2, 19, 13],
  [20, 12, 8, 24, 4, 28],
  [23, 9, 6, 18, 19, 21],
  [19, 5, 30, 10, 31, 1],
  [4, 28, 8, 24, 20, 12],
  [1, 25, 2, 26, 29, 13],
  [26, 24, 28, 24, 26],
  [21, 5, 10, 18, 1, 9],
  [10, 24, 28, 24, 10],
  [24, 0, 16, 0, 24],
  [13, 5, 26, 18, 25, 9],
  [18, 24, 12, 24, 18],
  [17, 1, 2, 10, 13, 21],
  [2, 24, 12, 24, 2],
  [11, 19, 22, 30, 31, 15],
  [30, 8, 20, 8, 30],
  [23, 7, 14, 6, 27, 19],
  [14, 8, 20, 8, 14],
  [8, 0, 16, 0, 8],
  [23, 31, 14, 22, 27, 11],
  [22, 8, 4, 8, 22],
  [19, 3, 6, 30, 7, 31],
  [6, 8, 4, 8, 6],
  [1, 15, 26, 14, 21, 19],
  [20, 0, 8, 0, 4],
  [26, 8, 12, 8, 10],
  [22, 24, 20, 24, 6],
  [21, 3, 2, 22, 25, 23],
  [28, 0, 24, 0, 12],
  [10, 8, 12, 8, 26],
  [6, 24, 20, 24, 22],
  [13, 3, 18, 22, 17, 23],
  [4, 0, 8, 0, 20],
  [18, 8, 28, 8, 2],
  [30, 24, 4, 24, 14],
  [17, 7, 26, 30, 5, 11],
  [12, 0, 24, 0, 28],
  [2, 8, 28, 8, 18],
  [14, 24, 4, 24, 30],
  [11, 5, 30, 26, 7, 17],
  [23, 17, 22, 18, 3, 13],
  [23, 25, 22, 2, 3, 21],
  [19, 21, 14, 26, 15, 1],
  [20, 16, 24, 16, 20],
  [28, 16, 8, 16, 28],
  [4, 16, 24, 16, 4],
  [12, 16, 8, 16, 12]]

def tr11 : List (ℕ × ℕ) := [
  (1, 2),
  (3, 4),
  (5, 6),
  (7, 8),
  (9, 10),
  (11, 12),
  (13, 14),
  (15, 16),
  (17, 18),
  (19, 20),
  (21, 18),
  (22, 23),
  (24, 18),
  (25, 26),
  (27, 18),
  (28, 29),
  (30, 31),
  (8, 32),
  (18, 18),
  (33, 34),
  (35, 36),
  (10, 32),
  (37, 38),
  (39, 40),
  (12, 41),
  (42, 43),
  (44, 45),
  (14, 41),
  (46, 47),
  (48, 49),
  (50, 51),
  (52, 53),
  (32, 41),
  (54, 55),
  (56, 57),
  (58, 59),
  (60, 61),
  (62, 51),
  (57, 56),
  (63, 47),
  (61, 60),
  (41, 32),
  (64, 59),
  (49, 48),
  (65, 55),
  (53, 52),
  (28, 31),
  (66, 67),
  (48, 53),
  (49, 52),
  (30, 29),
  (67, 66),
  (52, 49),
  (53, 48),
  (33, 36),
  (68, 69),
  (56, 61),
  (57, 60),
  (35, 34),
  (69, 68),
  (60, 57),
  (61, 56),
  (37, 40),
  (39, 38),
  (42, 45),
  (44, 43),
  (66, 69),
  (67, 68),
  (68, 67),
  (69, 66)]

theorem check11 : checkAut 5 tbl11 tr11 = true := by decide +kernel

theorem tbl11_start : normEq (pwL 16) (tbl11.getD 0 []) = true := by decide +kernel

theorem tbl11_length : tbl11.length = 70 := by decide +kernel

end MathDB335487
```

### `BinFamilyCheck.lean`

```lean
import BinAutomaton

/-!
# The level induction for `m = 16(4^j + 1) - 1`

`H_m ≡ (1 - x)^16 (1 - x^{4^j})^16 T (mod 32)`. Reading two binary digits of `n` maps
`l · D2^{2k+2}(G) · T` to `ψ(l) · D2^{2k}(G) · T` with `ψ = phi_f 1 ∘ phi_e 1`, so a finite set
of polynomials closed under the four maps `ψ` reduces every `j` to `j = 0`, i.e. to the
automaton for `l · (1 - x)^16 · T`. The K-direction (`D2^a`) is a sign-twisted copy.
-/

namespace MathDB335487

open PowerSeries

/-- Check of a two-digit closed set `S` (transitions `trS`) whose products with `(1 - x)^16`
lie (mod 32) in an automaton table `tbl` at indices `base`. -/
def checkFam (S : List (List ℕ)) (trS : List (ℕ × ℕ × ℕ × ℕ)) (base : List ℕ)
    (tbl : List (List ℕ)) : Bool :=
  (List.range S.length).all fun i =>
    decide ((trS.getD i (0, 0, 0, 0)).1 < S.length) &&
    decide ((trS.getD i (0, 0, 0, 0)).2.1 < S.length) &&
    decide ((trS.getD i (0, 0, 0, 0)).2.2.1 < S.length) &&
    decide ((trS.getD i (0, 0, 0, 0)).2.2.2 < S.length) &&
    normEq (phi0 1 (phi0 1 (S.getD i []))) (S.getD (trS.getD i (0, 0, 0, 0)).1 []) &&
    normEq (phi1 1 (phi0 1 (S.getD i []))) (S.getD (trS.getD i (0, 0, 0, 0)).2.1 []) &&
    normEq (phi0 1 (phi1 1 (S.getD i []))) (S.getD (trS.getD i (0, 0, 0, 0)).2.2.1 []) &&
    normEq (phi1 1 (phi1 1 (S.getD i []))) (S.getD (trS.getD i (0, 0, 0, 0)).2.2.2 []) &&
    decide (base.getD i 0 < tbl.length) &&
    normEq (mulL (S.getD i []) (pwL 16)) (tbl.getD (base.getD i 0) [])

/-- One binary digit: `coeff (2q+ε) (l · D2(C) · T) = coeff q (phi_ε 1 l · C · T)`. -/
theorem digit0 (l : List ℕ) (Cs : R32⟦X⟧) (q : ℕ) :
    coeff (2 * q) (toPS l * D2 Cs * T) = coeff q (toPS (phi0 1 l) * Cs * T) := by
  rw [mul_D2_T, step0, mul_assoc]

theorem digit1 (l : List ℕ) (Cs : R32⟦X⟧) (q : ℕ) :
    coeff (2 * q + 1) (toPS l * D2 Cs * T) = coeff q (toPS (phi1 1 l) * Cs * T) := by
  rw [mul_D2_T, step1, mul_assoc]

theorem fam_sound (S : List (List ℕ)) (trS : List (ℕ × ℕ × ℕ × ℕ)) (base : List ℕ)
    (tbl : List (List ℕ)) (tr : List (ℕ × ℕ))
    (hS : checkFam S trS base tbl = true) (hA : ∀ i < tbl.length, rowOK 1 tbl tr i = true) :
    ∀ k, ∀ i < S.length, ∀ n,
      coeff n (toPS (S.getD i []) * (⇑D2)^[2 * k] ((1 - X) ^ 16) * T) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro i hi n
    have hc := (List.all_eq_true.1 hS) i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨_, hb⟩, he⟩ := hc
    rw [Nat.mul_zero, Function.iterate_zero_apply, ← toPS_pwL, ← toPS_mulL, toPS_normEq _ _ he,
      ← pow_one T]
    exact aut_sound_rows 1 tbl tr hA n _ hb
  | succ k ih =>
    intro i hi n
    have hc := (List.all_eq_true.1 hS) i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, e1⟩, e2⟩, e3⟩, e4⟩, _⟩, _⟩ := hc
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [digit0]
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' a
      · rw [digit0, toPS_normEq _ _ e1]; exact ih _ h1 q
      · rw [digit1, toPS_normEq _ _ e2]; exact ih _ h2 q
    · rw [digit1]
      obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' a
      · rw [digit0, toPS_normEq _ _ e3]; exact ih _ h3 q
      · rw [digit1, toPS_normEq _ _ e4]; exact ih _ h4 q

theorem toPS_one : toPS [1] = 1 := by simp [toPS]

/-- The K-direction: `F(x^{2^a}) · T` inherits "no coefficient `≡ 0`" from `F · T`. -/
theorem dil_sound (F : R32⟦X⟧) (hF : ∀ n, coeff n (F * T) ≠ 0) :
    ∀ a n, coeff n ((⇑D2)^[a] F * T) ≠ 0 := by
  intro a
  induction a with
  | zero => simpa using hF
  | succ a ih =>
    intro n
    rw [Function.iterate_succ_apply', ← one_mul (D2 _), ← toPS_one]
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [digit0, toPS_normEq _ [1] (by decide), toPS_one, one_mul]; exact ih q
    · have h31 : toPS [31] = -1 := by
        have : (31 : R32) = -1 := by decide
        rw [toPS, toPS, mul_zero, add_zero, Nat.cast_ofNat, this, map_neg, map_one]
      rw [digit1, toPS_normEq _ [31] (by decide), h31, neg_one_mul, neg_mul, map_neg,
        neg_ne_zero]
      exact ih q

end MathDB335487
```

### `BinDataFamily.lean`

```lean
import BinFamilyCheck

/-! Certificate for the family: `famS` (31 polynomials) is the closure of `(1 - x)^16` under the
four two-digit maps `phi_f 1 ∘ phi_e 1`; `famTbl` (400 states) is closed under `phi0 1`, `phi1 1`,
contains every `famS i · (1 - x)^16` (at index `famBase i`), and no state has constant term
`≡ 0 (mod 32)`. Generated by `scripts/automata.py`, checked here by kernel evaluation. -/

namespace MathDB335487

def famS : List (List ℕ) := [
  [1, 16, 24, 16, 28, 16, 8, 16, 6, 16, 8, 16, 28, 16, 24, 16, 1],
  [1, 4, 30, 20, 9],
  [7, 12, 2, 28, 15],
  [15, 28, 2, 12, 7],
  [9, 20, 30, 4, 1],
  [1, 27],
  [25, 11],
  [3, 1],
  [19, 9],
  [7, 29],
  [15, 13],
  [5, 23],
  [21, 15],
  [15, 21],
  [23, 5],
  [13, 15],
  [29, 7],
  [9, 19],
  [1, 3],
  [11, 25],
  [27, 1],
  [4],
  [26],
  [6],
  [28],
  [18],
  [14],
  [30],
  [2],
  [22],
  [10]]

def famTr : List (ℕ × ℕ × ℕ × ℕ) := [
  (1, 2, 3, 4),
  (5, 6, 7, 8),
  (9, 10, 11, 12),
  (13, 14, 15, 16),
  (17, 18, 19, 20),
  (5, 21, 22, 23),
  (6, 24, 25, 26),
  (7, 24, 27, 28),
  (8, 21, 29, 30),
  (9, 24, 29, 30),
  (10, 21, 27, 28),
  (11, 21, 25, 26),
  (12, 24, 22, 23),
  (13, 24, 23, 22),
  (14, 21, 26, 25),
  (15, 21, 28, 27),
  (16, 24, 30, 29),
  (17, 21, 30, 29),
  (18, 24, 28, 27),
  (19, 24, 26, 25),
  (20, 21, 23, 22),
  (21, 24, 24, 21),
  (22, 23, 23, 22),
  (23, 22, 22, 23),
  (24, 21, 21, 24),
  (25, 26, 26, 25),
  (26, 25, 25, 26),
  (27, 28, 28, 27),
  (28, 27, 27, 28),
  (29, 30, 30, 29),
  (30, 29, 29, 30)]

def famBase : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]

def famTbl : List (List ℕ) := [
  [1, 0, 16, 0, 24, 0, 16, 0, 28, 0, 16, 0, 8, 0, 16, 0, 6, 0, 16, 0, 8, 0, 16, 0, 28, 0, 16, 0, 24, 0, 16, 0, 1],
  [1, 20, 22, 4, 21, 16, 8, 16, 18, 24, 4, 24, 2, 16, 8, 16, 13, 20, 22, 4, 9],
  [7, 28, 10, 12, 3, 16, 24, 16, 30, 8, 28, 8, 14, 16, 24, 16, 27, 28, 10, 12, 15],
  [15, 12, 10, 28, 27, 16, 24, 16, 14, 8, 28, 8, 30, 16, 24, 16, 3, 12, 10, 28, 7],
  [9, 4, 22, 20, 13, 16, 8, 16, 2, 24, 4, 24, 18, 16, 8, 16, 21, 4, 22, 20, 1],
  [1, 11, 8, 24, 12, 4, 24, 8, 22, 18, 24, 8, 12, 4, 8, 24, 17, 27],
  [25, 27, 8, 24, 12, 4, 24, 8, 6, 18, 24, 8, 12, 4, 8, 24, 9, 11],
  [3, 17, 24, 8, 4, 12, 8, 24, 2, 22, 8, 24, 4, 12, 24, 8, 19, 1],
  [19, 25, 24, 8, 4, 12, 8, 24, 2, 6, 8, 24, 4, 12, 24, 8, 3, 9],
  [7, 13, 24, 8, 20, 28, 8, 24, 26, 30, 8, 24, 20, 28, 24, 8, 23, 29],
  [15, 29, 24, 8, 20, 28, 8, 24, 10, 30, 8, 24, 20, 28, 24, 8, 31, 13],
  [5, 7, 8, 24, 28, 20, 24, 8, 14, 26, 24, 8, 28, 20, 8, 24, 21, 23],
  [21, 31, 8, 24, 28, 20, 24, 8, 14, 10, 24, 8, 28, 20, 8, 24, 5, 15],
  [15, 5, 24, 8, 20, 28, 8, 24, 10, 14, 8, 24, 20, 28, 24, 8, 31, 21],
  [23, 21, 24, 8, 20, 28, 8, 24, 26, 14, 8, 24, 20, 28, 24, 8, 7, 5],
  [13, 31, 8, 24, 28, 20, 24, 8, 30, 10, 24, 8, 28, 20, 8, 24, 29, 15],
  [29, 23, 8, 24, 28, 20, 24, 8, 30, 26, 24, 8, 28, 20, 8, 24, 13, 7],
  [9, 3, 8, 24, 12, 4, 24, 8, 6, 2, 24, 8, 12, 4, 8, 24, 25, 19],
  [1, 19, 8, 24, 12, 4, 24, 8, 22, 2, 24, 8, 12, 4, 8, 24, 17, 3],
  [11, 9, 24, 8, 4, 12, 8, 24, 18, 6, 8, 24, 4, 12, 24, 8, 27, 25],
  [27, 17, 24, 8, 4, 12, 8, 24, 18, 22, 8, 24, 4, 12, 24, 8, 11, 1],
  [4, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 4],
  [26, 0, 16, 0, 24, 0, 16, 0, 28, 0, 16, 0, 24, 0, 16, 0, 26],
  [6, 0, 16, 0, 8, 0, 16, 0, 4, 0, 16, 0, 8, 0, 16, 0, 6],
  [28, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 28],
  [18, 0, 16, 0, 24, 0, 16, 0, 12, 0, 16, 0, 24, 0, 16, 0, 18],
  [14, 0, 16, 0, 8, 0, 16, 0, 20, 0, 16, 0, 8, 0, 16, 0, 14],
  [30, 0, 16, 0, 8, 0, 16, 0, 20, 0, 16, 0, 8, 0, 16, 0, 30],
  [2, 0, 16, 0, 24, 0, 16, 0, 12, 0, 16, 0, 24, 0, 16, 0, 2],
  [22, 0, 16, 0, 8, 0, 16, 0, 4, 0, 16, 0, 8, 0, 16, 0, 22],
  [10, 0, 16, 0, 24, 0, 16, 0, 28, 0, 16, 0, 24, 0, 16, 0, 10],
  [1, 16, 24, 16, 28, 16, 8, 16, 6, 16, 8, 16, 28, 16, 24, 16, 1],
  [31, 16, 8, 16, 4, 16, 24, 16, 26, 16, 24, 16, 4, 16, 8, 16, 31],
  [1, 2, 17, 24, 2, 12, 10, 24, 29, 2, 5],
  [19, 14, 27, 8, 6, 20, 14, 8, 7, 14, 23],
  [7, 14, 23, 8, 14, 20, 6, 8, 11, 14, 3],
  [21, 2, 13, 24, 10, 12, 2, 24, 1, 2, 17],
  [15, 30, 31, 8, 30, 20, 22, 8, 19, 30, 11],
  [29, 18, 21, 24, 26, 12, 18, 24, 9, 18, 25],
  [9, 18, 25, 24, 18, 12, 26, 24, 5, 18, 13],
  [27, 30, 3, 8, 22, 20, 30, 8, 15, 30, 31],
  [1, 29, 20, 20, 14, 6, 4, 4, 25, 5],
  [10, 16, 24, 16, 28, 16, 24, 16, 10],
  [25, 13, 20, 20, 30, 6, 4, 4, 17, 21],
  [2, 16, 24, 16, 12, 16, 24, 16, 2],
  [3, 7, 28, 28, 10, 18, 12, 12, 11, 31],
  [14, 16, 8, 16, 20, 16, 8, 16, 14],
  [19, 31, 28, 28, 10, 2, 12, 12, 27, 23],
  [6, 16, 8, 16, 4, 16, 8, 16, 6],
  [7, 11, 12, 12, 2, 10, 28, 28, 15, 3],
  [15, 27, 12, 12, 18, 10, 28, 28, 23, 19],
  [5, 1, 4, 4, 6, 30, 20, 20, 29, 9],
  [21, 9, 4, 4, 6, 14, 20, 20, 13, 17],
  [15, 19, 12, 12, 18, 26, 28, 28, 23, 11],
  [22, 16, 8, 16, 4, 16, 8, 16, 22],
  [23, 3, 12, 12, 2, 26, 28, 28, 31, 27],
  [30, 16, 8, 16, 20, 16, 8, 16, 30],
  [13, 9, 4, 4, 22, 14, 20, 20, 5, 17],
  [18, 16, 24, 16, 12, 16, 24, 16, 18],
  [29, 17, 4, 4, 22, 30, 20, 20, 21, 25],
  [26, 16, 24, 16, 28, 16, 24, 16, 26],
  [9, 5, 20, 20, 30, 22, 4, 4, 1, 13],
  [1, 21, 20, 20, 14, 22, 4, 4, 25, 29],
  [11, 15, 28, 28, 26, 2, 12, 12, 19, 7],
  [27, 7, 28, 28, 26, 18, 12, 12, 3, 31],
  [4, 0, 16, 0, 24, 0, 16, 0, 4],
  [28, 0, 16, 0, 8, 0, 16, 0, 28],
  [1, 8, 12, 24, 22, 24, 12, 8, 17],
  [15, 24, 20, 8, 10, 8, 20, 24, 31],
  [31, 24, 20, 8, 10, 8, 20, 24, 15],
  [17, 8, 12, 24, 22, 24, 12, 8, 1],
  [1, 15, 10, 30, 5, 3],
  [1, 7, 10, 14, 5, 27],
  [19, 13, 30, 26, 31, 9],
  [27, 13, 14, 26, 7, 9],
  [7, 9, 6, 18, 3, 21],
  [7, 17, 6, 2, 3, 29],
  [21, 11, 18, 22, 9, 15],
  [13, 11, 2, 22, 1, 15],
  [15, 1, 22, 2, 11, 13],
  [15, 9, 22, 18, 11, 21],
  [29, 3, 2, 6, 17, 7],
  [21, 3, 18, 6, 9, 7],
  [9, 7, 26, 14, 13, 27],
  [9, 31, 26, 30, 13, 19],
  [27, 5, 14, 10, 7, 1],
  [3, 5, 30, 10, 15, 1],
  [1, 23, 26, 30, 21, 27],
  [28, 0, 24, 0, 12],
  [10, 8, 12, 8, 26],
  [6, 24, 20, 24, 22],
  [25, 7, 10, 30, 13, 11],
  [20, 0, 8, 0, 4],
  [2, 8, 28, 8, 18],
  [14, 24, 4, 24, 30],
  [3, 21, 14, 26, 31, 1],
  [4, 0, 8, 0, 20],
  [19, 29, 14, 10, 15, 9],
  [12, 0, 24, 0, 28],
  [7, 1, 22, 18, 19, 29],
  [15, 17, 6, 18, 27, 13],
  [5, 3, 2, 22, 9, 23],
  [21, 27, 2, 6, 25, 15],
  [15, 25, 6, 2, 27, 21],
  [22, 24, 20, 24, 6],
  [26, 8, 12, 8, 10],
  [23, 9, 22, 2, 3, 5],
  [30, 24, 4, 24, 14],
  [18, 8, 28, 8, 2],
  [13, 27, 18, 6, 17, 15],
  [29, 19, 18, 22, 1, 7],
  [9, 15, 10, 14, 29, 19],
  [1, 31, 26, 14, 21, 3],
  [11, 13, 30, 10, 7, 25],
  [27, 21, 30, 26, 23, 1],
  [4, 16, 24, 16, 4],
  [28, 16, 8, 16, 28],
  [1, 4, 30, 20, 9],
  [7, 12, 2, 28, 15],
  [15, 28, 2, 12, 7],
  [9, 20, 30, 4, 1],
  [31, 28, 2, 12, 23],
  [25, 20, 30, 4, 17],
  [17, 4, 30, 20, 25],
  [23, 12, 2, 28, 31],
  [1, 27, 7, 29],
  [14, 20, 30],
  [1, 3, 23, 5],
  [6, 4, 22],
  [19, 17, 5, 23],
  [26, 28, 10],
  [27, 1, 13, 23],
  [18, 12, 2],
  [7, 29, 17, 11],
  [2, 12, 18],
  [7, 21, 1, 3],
  [10, 28, 26],
  [21, 7, 19, 17],
  [22, 4, 6],
  [13, 23, 11, 17],
  [30, 20, 14],
  [15, 21, 9, 19],
  [15, 13, 25, 11],
  [29, 31, 11, 25],
  [21, 15, 3, 25],
  [9, 19, 31, 5],
  [9, 27, 15, 13],
  [27, 9, 29, 31],
  [3, 25, 5, 31],
  [28, 24, 12],
  [4, 8, 20],
  [10, 4, 18],
  [30, 28, 6],
  [6, 28, 30],
  [18, 4, 10],
  [25, 3, 15, 21],
  [20, 8, 4],
  [12, 24, 28],
  [2, 20, 10],
  [6, 12, 14],
  [14, 12, 6],
  [10, 20, 2],
  [5, 31, 19, 9],
  [22, 28, 14],
  [2, 4, 26],
  [26, 4, 2],
  [14, 28, 22],
  [23, 13, 1, 27],
  [30, 12, 22],
  [26, 20, 18],
  [18, 20, 26],
  [22, 12, 30],
  [11, 17, 29, 7],
  [1, 26, 21],
  [3, 22, 23],
  [7, 22, 19],
  [5, 26, 17],
  [15, 6, 27],
  [13, 10, 25],
  [9, 10, 29],
  [11, 6, 31],
  [31, 6, 11],
  [29, 10, 9],
  [25, 10, 13],
  [27, 6, 15],
  [17, 26, 5],
  [19, 22, 7],
  [23, 22, 3],
  [21, 26, 1],
  [1, 12, 3],
  [26, 22],
  [14, 10],
  [6, 2],
  [1, 20, 27],
  [2, 14],
  [6, 18],
  [30, 10],
  [19, 20, 9],
  [30, 18],
  [26, 14],
  [2, 22],
  [27, 12, 9],
  [6, 10],
  [18, 22],
  [26, 30],
  [7, 20, 21],
  [22, 26],
  [2, 6],
  [10, 14],
  [7, 12, 29],
  [14, 2],
  [10, 30],
  [18, 6],
  [21, 12, 15],
  [18, 30],
  [22, 2],
  [14, 26],
  [13, 20, 15],
  [10, 6],
  [30, 26],
  [22, 18],
  [15, 20, 13],
  [15, 12, 21],
  [29, 12, 7],
  [21, 20, 7],
  [9, 12, 27],
  [9, 20, 19],
  [27, 20, 1],
  [3, 12, 1],
  [28, 20],
  [4, 12],
  [25, 12, 11],
  [20, 28],
  [12, 4],
  [5, 20, 23],
  [23, 20, 5],
  [11, 12, 25],
  [1, 27],
  [25, 11],
  [3, 1],
  [19, 9],
  [7, 29],
  [15, 13],
  [5, 23],
  [21, 15],
  [15, 21],
  [23, 5],
  [13, 15],
  [29, 7],
  [9, 19],
  [1, 3],
  [11, 25],
  [27, 1],
  [31, 5],
  [7, 21],
  [29, 31],
  [13, 23],
  [25, 3],
  [17, 19],
  [27, 9],
  [11, 17],
  [17, 11],
  [9, 27],
  [19, 17],
  [3, 25],
  [23, 13],
  [31, 29],
  [21, 7],
  [5, 31],
  [1, 23],
  [11, 29],
  [26, 10],
  [28],
  [14, 22],
  [6, 30],
  [1, 7],
  [19, 5],
  [2, 18],
  [12],
  [6, 14],
  [30, 22],
  [19, 21],
  [30, 14],
  [20],
  [26, 18],
  [2, 10],
  [27, 29],
  [17, 23],
  [6, 22],
  [4],
  [18, 10],
  [26, 2],
  [7, 1],
  [13, 11],
  [22, 6],
  [2, 26],
  [10, 18],
  [7, 17],
  [5, 3],
  [14, 30],
  [10, 2],
  [18, 26],
  [21, 3],
  [23, 17],
  [18, 2],
  [22, 30],
  [14, 6],
  [13, 27],
  [10, 26],
  [30, 6],
  [22, 14],
  [15, 25],
  [5, 19],
  [15, 9],
  [29, 11],
  [29, 27],
  [21, 19],
  [31, 25],
  [9, 15],
  [3, 5],
  [9, 31],
  [11, 13],
  [27, 13],
  [25, 31],
  [3, 21],
  [28, 12],
  [24],
  [4, 20],
  [8],
  [20, 4],
  [12, 28],
  [1, 5],
  [26],
  [25, 21],
  [18],
  [3, 31],
  [30],
  [19, 23],
  [22],
  [7, 3],
  [15, 19],
  [5, 9],
  [21, 17],
  [15, 11],
  [6],
  [23, 27],
  [14],
  [13, 17],
  [2],
  [29, 25],
  [10],
  [9, 13],
  [1, 29],
  [11, 7],
  [27, 31],
  [31, 27],
  [7, 11],
  [29, 1],
  [13, 9],
  [25, 29],
  [17, 13],
  [27, 23],
  [11, 15],
  [17, 21],
  [9, 5],
  [19, 15],
  [3, 7],
  [23, 19],
  [31, 3],
  [21, 25],
  [5, 1],
  [1, 9],
  [11, 3],
  [16],
  [1, 25],
  [19, 27],
  [19, 11],
  [27, 3],
  [17, 9],
  [7, 31],
  [13, 21],
  [7, 15],
  [5, 29],
  [21, 29],
  [23, 15],
  [13, 5],
  [15, 7],
  [5, 13],
  [15, 23],
  [29, 21],
  [29, 5],
  [21, 13],
  [31, 7],
  [9, 17],
  [3, 27],
  [9, 1],
  [11, 19],
  [27, 19],
  [25, 1],
  [3, 11]]

def famTblTr : List (ℕ × ℕ) := [
  (31, 32),
  (33, 34),
  (35, 36),
  (37, 38),
  (39, 40),
  (41, 42),
  (43, 44),
  (45, 46),
  (47, 48),
  (49, 48),
  (50, 46),
  (51, 44),
  (52, 42),
  (53, 54),
  (55, 56),
  (57, 58),
  (59, 60),
  (61, 60),
  (62, 58),
  (63, 56),
  (64, 54),
  (65, 66),
  (60, 48),
  (48, 60),
  (66, 65),
  (58, 46),
  (46, 58),
  (56, 44),
  (44, 56),
  (54, 42),
  (42, 54),
  (67, 68),
  (69, 70),
  (71, 72),
  (73, 74),
  (75, 76),
  (77, 78),
  (79, 80),
  (81, 82),
  (83, 84),
  (85, 86),
  (87, 88),
  (89, 90),
  (91, 92),
  (93, 94),
  (95, 96),
  (94, 93),
  (97, 98),
  (90, 89),
  (99, 96),
  (100, 98),
  (101, 88),
  (102, 92),
  (103, 96),
  (104, 105),
  (106, 98),
  (107, 108),
  (109, 88),
  (108, 107),
  (110, 92),
  (105, 104),
  (111, 88),
  (112, 92),
  (113, 96),
  (114, 98),
  (115, 116),
  (116, 115),
  (117, 118),
  (119, 120),
  (121, 122),
  (123, 124),
  (125, 126),
  (127, 128),
  (129, 130),
  (131, 132),
  (133, 134),
  (135, 136),
  (137, 138),
  (139, 140),
  (141, 132),
  (142, 130),
  (143, 128),
  (144, 126),
  (145, 140),
  (146, 138),
  (147, 136),
  (148, 134),
  (127, 138),
  (149, 150),
  (151, 152),
  (153, 154),
  (155, 126),
  (156, 157),
  (158, 159),
  (160, 161),
  (148, 132),
  (150, 149),
  (129, 136),
  (157, 156),
  (135, 130),
  (141, 134),
  (162, 140),
  (137, 128),
  (142, 136),
  (163, 164),
  (165, 166),
  (167, 132),
  (168, 169),
  (170, 171),
  (139, 126),
  (143, 138),
  (146, 128),
  (125, 140),
  (172, 134),
  (147, 130),
  (150, 157),
  (149, 156),
  (173, 174),
  (175, 176),
  (177, 178),
  (179, 180),
  (181, 182),
  (183, 184),
  (185, 186),
  (187, 188),
  (189, 190),
  (191, 192),
  (193, 194),
  (195, 196),
  (197, 198),
  (199, 200),
  (201, 202),
  (203, 204),
  (205, 206),
  (207, 208),
  (209, 210),
  (211, 212),
  (213, 214),
  (215, 216),
  (217, 218),
  (219, 220),
  (221, 202),
  (222, 198),
  (223, 194),
  (224, 190),
  (225, 218),
  (226, 214),
  (227, 210),
  (228, 206),
  (229, 229),
  (230, 230),
  (208, 199),
  (196, 219),
  (192, 215),
  (212, 203),
  (231, 218),
  (232, 232),
  (233, 233),
  (200, 203),
  (192, 195),
  (216, 219),
  (208, 211),
  (234, 190),
  (220, 195),
  (200, 207),
  (204, 211),
  (216, 191),
  (235, 206),
  (196, 191),
  (204, 199),
  (212, 207),
  (220, 215),
  (236, 202),
  (237, 238),
  (239, 240),
  (241, 242),
  (243, 244),
  (245, 246),
  (247, 248),
  (249, 250),
  (251, 252),
  (253, 254),
  (255, 256),
  (257, 258),
  (259, 260),
  (261, 262),
  (263, 264),
  (265, 266),
  (267, 268),
  (269, 270),
  (271, 272),
  (273, 272),
  (274, 272),
  (275, 276),
  (277, 278),
  (279, 278),
  (280, 278),
  (281, 269),
  (282, 283),
  (284, 283),
  (285, 283),
  (286, 287),
  (288, 289),
  (290, 289),
  (291, 289),
  (292, 293),
  (294, 289),
  (295, 289),
  (296, 289),
  (297, 298),
  (299, 283),
  (300, 283),
  (301, 283),
  (302, 303),
  (304, 278),
  (305, 278),
  (306, 278),
  (307, 297),
  (308, 272),
  (309, 272),
  (310, 272),
  (311, 312),
  (313, 314),
  (315, 311),
  (316, 317),
  (318, 319),
  (320, 321),
  (322, 323),
  (324, 320),
  (325, 326),
  (327, 328),
  (323, 281),
  (329, 328),
  (330, 326),
  (298, 313),
  (303, 315),
  (321, 275),
  (331, 332),
  (333, 334),
  (335, 336),
  (337, 338),
  (339, 338),
  (340, 336),
  (341, 334),
  (342, 332),
  (343, 344),
  (345, 346),
  (347, 348),
  (349, 350),
  (351, 350),
  (352, 348),
  (353, 346),
  (354, 344),
  (355, 344),
  (356, 346),
  (357, 348),
  (358, 350),
  (359, 350),
  (360, 348),
  (361, 346),
  (362, 344),
  (363, 332),
  (364, 334),
  (365, 336),
  (366, 338),
  (367, 338),
  (368, 336),
  (369, 334),
  (370, 332),
  (371, 338),
  (372, 334),
  (190, 373),
  (272, 289),
  (191, 328),
  (192, 326),
  (374, 344),
  (375, 334),
  (194, 373),
  (278, 283),
  (195, 328),
  (196, 326),
  (376, 348),
  (198, 373),
  (283, 278),
  (199, 326),
  (200, 328),
  (377, 348),
  (378, 344),
  (202, 373),
  (289, 272),
  (203, 326),
  (204, 328),
  (379, 332),
  (380, 336),
  (206, 373),
  (207, 326),
  (208, 328),
  (381, 350),
  (382, 336),
  (210, 373),
  (211, 326),
  (212, 328),
  (383, 346),
  (384, 332),
  (214, 373),
  (215, 328),
  (216, 326),
  (385, 346),
  (218, 373),
  (219, 328),
  (220, 326),
  (386, 350),
  (387, 346),
  (388, 332),
  (389, 346),
  (390, 336),
  (391, 336),
  (392, 332),
  (393, 344),
  (394, 348),
  (395, 338),
  (396, 348),
  (397, 334),
  (398, 344),
  (399, 334),
  (229, 373),
  (326, 328),
  (230, 373),
  (328, 326),
  (232, 373),
  (233, 373),
  (237, 289),
  (332, 344),
  (238, 272),
  (334, 346),
  (239, 272),
  (336, 348),
  (240, 289),
  (338, 350),
  (241, 272),
  (242, 289),
  (243, 289),
  (244, 272),
  (245, 272),
  (344, 332),
  (246, 289),
  (346, 334),
  (247, 289),
  (348, 336),
  (248, 272),
  (350, 338),
  (249, 289),
  (250, 272),
  (251, 272),
  (252, 289),
  (253, 272),
  (254, 289),
  (255, 289),
  (256, 272),
  (257, 289),
  (258, 272),
  (259, 272),
  (260, 289),
  (261, 289),
  (262, 272),
  (263, 272),
  (264, 289),
  (265, 272),
  (266, 289),
  (267, 289),
  (268, 272),
  (269, 328),
  (270, 326),
  (373, 373),
  (275, 326),
  (276, 328),
  (281, 326),
  (286, 328),
  (287, 326),
  (292, 326),
  (293, 328),
  (297, 328),
  (298, 326),
  (302, 328),
  (303, 326),
  (307, 326),
  (311, 326),
  (312, 328),
  (313, 328),
  (314, 326),
  (315, 328),
  (316, 326),
  (317, 328),
  (318, 328),
  (319, 326),
  (320, 326),
  (321, 328),
  (322, 326),
  (323, 328),
  (324, 328)]

theorem famRows0 : (List.range' 0 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows1 : (List.range' 50 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows2 : (List.range' 100 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows3 : (List.range' 150 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows4 : (List.range' 200 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows5 : (List.range' 250 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows6 : (List.range' 300 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famRows7 : (List.range' 350 50).all (rowOK 1 famTbl famTblTr) = true := by
  decide +kernel

theorem famTbl_length : famTbl.length = 400 := by decide +kernel

theorem famRows : ∀ i < famTbl.length, rowOK 1 famTbl famTblTr i = true := by
  intro i hi
  rw [famTbl_length] at hi
  have key : ∀ k, (List.range' (50 * k) 50).all (rowOK 1 famTbl famTblTr) = true →
      50 * k ≤ i → i < 50 * k + 50 → rowOK 1 famTbl famTblTr i = true := by
    intro k hk h1 h2
    exact List.all_eq_true.1 hk i (List.mem_range'_1.2 ⟨h1, h2⟩)
  have hk : i / 50 < 8 := by omega
  have h1 : 50 * (i / 50) ≤ i := Nat.mul_div_le i 50
  have h2 : i < 50 * (i / 50) + 50 := by omega
  interval_cases hq : i / 50
  · exact key 0 famRows0 h1 h2
  · exact key 1 famRows1 h1 h2
  · exact key 2 famRows2 h1 h2
  · exact key 3 famRows3 h1 h2
  · exact key 4 famRows4 h1 h2
  · exact key 5 famRows5 h1 h2
  · exact key 6 famRows6 h1 h2
  · exact key 7 famRows7 h1 h2

theorem checkFamS : checkFam famS famTr famBase famTbl = true := by decide +kernel

theorem famS_start : normEq (pwL 16) (famS.getD 0 []) = true := by decide +kernel

theorem famS_length : famS.length = 31 := by decide +kernel

end MathDB335487
```

### `BinMain.lean`

```lean
import BinData11
import BinDataFamily

/-!
# MathDB 335487: Conjecture 5.3 of Gawron–Miska–Ulas is false

* `b11_not_dvd`: `32 ∤ b₁₁(n)` for every `n`, so `ν₂(b₁₁(n)) ≤ 4`;
* `mathdb_335487_refuted`: the literal negation of the conjecture;
* `family_not_dvd`: for all `K ≥ 4`, `j ≥ 1`, `n`, `32 ∤ b_m(n)` with `m = 2^K (4^j + 1) - 1`;
* `family_counterexample`: each such `m` satisfies the hypotheses of the conjecture and has
  `ν₂(b_m(n)) ≤ 4` for all `n`.
-/

namespace MathDB335487

open PowerSeries

theorem not_dvd_of_cast_ne_zero {a : ℕ} (h : (a : R32) ≠ 0) : ¬ 32 ∣ a :=
  fun hd => h ((ZMod.natCast_eq_zero_iff a 32).2 hd)

theorem padicValNat_le_four {a : ℕ} (h : ¬ 32 ∣ a) : padicValNat 2 a ≤ 4 := by
  by_contra hv
  apply h
  have h1 : 2 ^ 5 ∣ 2 ^ padicValNat 2 a := pow_dvd_pow 2 (by omega)
  exact (h1.trans pow_padicValNat_dvd)

/-! ## m = 11 -/

theorem b11_cast_ne_zero (n : ℕ) : (b 11 n : R32) ≠ 0 := by
  rw [← coeff_H1_pow, star 11 16 (by norm_num) (by norm_num), ← toPS_pwL,
    toPS_normEq _ _ tbl11_start, show 16 - 11 = 5 from rfl]
  exact aut_sound 5 tbl11 tr11 check11 n 0 (by rw [tbl11_length]; norm_num)

/-- `ν₂(b₁₁(n)) ≤ 4` for every `n`: `2⁵ ∤ b₁₁(n)`. -/
theorem b11_not_dvd (n : ℕ) : ¬ 32 ∣ b 11 n := not_dvd_of_cast_ne_zero (b11_cast_ne_zero n)

theorem eleven_not_mersenne : ∀ k : ℕ, 0 < k → 11 ≠ 2 ^ k - 1 := by
  intro k hk h
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · interval_cases k <;> norm_num at h
  · have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h4
    omega

/-- **MathDB 335487 refuted**: the literal negation of Conjecture 5.3. -/
theorem mathdb_335487_refuted :
    ¬ (∀ m : ℕ, 2 ≤ m → (∀ k : ℕ, 0 < k → m ≠ 2 ^ k - 1) →
        ∀ B : ℕ, ∃ n : ℕ, B < padicValNat 2 (b m n)) := by
  intro h
  obtain ⟨n, hn⟩ := h 11 (by norm_num) eleven_not_mersenne 4
  have := padicValNat_le_four (b11_not_dvd n)
  omega

theorem not_conjecture53 : ¬ Conjecture53 := mathdb_335487_refuted

/-! ## The family m = 2^K (4^j + 1) - 1 -/

theorem fam_base (j : ℕ) (n : ℕ) :
    coeff n ((1 - X) ^ (16 * (4 ^ j + 1)) * T) ≠ 0 := by
  have e : 16 * (4 ^ j + 1) = 16 + 2 ^ (2 * j + 4) * 1 := by
    rw [pow_add, pow_mul]; norm_num; ring
  have hS0 : toPS (famS.getD 0 []) = (1 - X) ^ 16 := by
    rw [← toPS_normEq _ _ famS_start, toPS_pwL]
  have h := fam_sound famS famTr famBase famTbl famTblTr checkFamS famRows j 0
    (by rw [famS_length]; norm_num) n
  rw [hS0] at h
  rw [e, pow_add, pw_dil (2 * j) 1, Nat.mul_one]
  exact h

theorem family_cast_ne_zero (K j n : ℕ) (hK : 4 ≤ K) :
    (b (2 ^ K * (4 ^ j + 1) - 1) n : R32) ≠ 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, K = a + 4 := ⟨K - 4, by omega⟩
  have hpos : 0 < 2 ^ (a + 4) * (4 ^ j + 1) := by positivity
  have h16 : 16 ∣ 2 ^ (a + 4) * (4 ^ j + 1) :=
    Dvd.dvd.mul_right (by rw [pow_add]; exact Dvd.intro_left _ rfl) _
  rw [← coeff_H1_pow, star _ _ (Nat.sub_le _ 1) h16,
    show 2 ^ (a + 4) * (4 ^ j + 1) - (2 ^ (a + 4) * (4 ^ j + 1) - 1) = 1 by omega, pow_one,
    pw_dil a (4 ^ j + 1)]
  exact dil_sound _ (fam_base j) a n

/-- **Theorem A**: for all `K ≥ 4`, `j ≥ 1` and `n`, `2⁵ ∤ b_m(n)` where `m = 2^K (4^j + 1) - 1`. -/
theorem family_not_dvd (K j n : ℕ) (hK : 4 ≤ K) (_hj : 1 ≤ j) :
    ¬ 32 ∣ b (2 ^ K * (4 ^ j + 1) - 1) n :=
  not_dvd_of_cast_ne_zero (family_cast_ne_zero K j n hK)

/-- Each member of the family satisfies the hypotheses of Conjecture 5.3 and has bounded
`ν₂(b_m(n)) ≤ 4`. -/
theorem family_counterexample (K j : ℕ) (hK : 4 ≤ K) (hj : 1 ≤ j) :
    2 ≤ 2 ^ K * (4 ^ j + 1) - 1 ∧
    (∀ k : ℕ, 0 < k → 2 ^ K * (4 ^ j + 1) - 1 ≠ 2 ^ k - 1) ∧
    ∀ n : ℕ, padicValNat 2 (b (2 ^ K * (4 ^ j + 1) - 1) n) ≤ 4 := by
  have hK16 : 16 ≤ 2 ^ K := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  have hj4 : 4 ≤ 4 ^ j := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hbig : 80 ≤ 2 ^ K * (4 ^ j + 1) := by
    calc 80 = 16 * 5 := by norm_num
      _ ≤ 2 ^ K * (4 ^ j + 1) := Nat.mul_le_mul hK16 (by omega)
  refine ⟨by omega, ?_, fun n => padicValNat_le_four (family_not_dvd K j n hK hj)⟩
  intro k hk h
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hN : 2 ^ K * (4 ^ j + 1) = 2 ^ k := by omega
  have hdvd : 4 ^ j + 1 ∣ 2 ^ k := hN ▸ Dvd.intro_left _ rfl
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h2 : 2 ∣ 4 ^ j := dvd_pow (by norm_num : 2 ∣ 4) (by omega)
  cases i with
  | zero => simp at hi
  | succ i =>
    have : 2 ∣ 2 ^ (i + 1) := dvd_pow_self 2 (by omega)
    rw [← hi] at this
    omega

end MathDB335487
```

### `BinValues.lean`

```lean
import BinBridge
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.List.GetD
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Small values of `bin` and `b m`, checked by kernel evaluation

`binTab N` and `bTab m N` are list tables proved equal to `bin` and `b m` on `0, …, N`;
values are then computed by `decide +kernel`. Checks: `bin` against OEIS A018819
(the source cites A018819 for `b₁`), the source's Lemma 4.1 (`b_m(0) = 1`, `b_m(1) = m`),
and `b₁₁(12) = 11 599 632 = 2⁴ · 724 977` (so the bound `ν₂(b₁₁(n)) ≤ 4` is attained).
-/

namespace MathDB335487

/-- Extend a table `[bin 0, …, bin n]` by `bin (n+1)` using the recurrence. -/
def binExt (n : ℕ) (t : List ℕ) : List ℕ :=
  t ++ [t.getD n 0 + if (n + 1) % 2 = 0 then t.getD ((n + 1) / 2) 0 else 0]

def binTab : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => binExt n (binTab n)

theorem binTab_spec (N : ℕ) :
    (binTab N).length = N + 1 ∧ ∀ i ≤ N, (binTab N).getD i 0 = bin i := by
  induction N with
  | zero =>
    refine ⟨rfl, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simp [binTab, bin_zero]
  | succ n ih =>
    obtain ⟨hl, hv⟩ := ih
    refine ⟨by simp [binTab, binExt, hl], fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · rw [binTab, binExt, List.getD_append _ _ _ _ (by omega), hv i (by omega)]
    · obtain rfl : i = n + 1 := by omega
      rw [binTab, binExt, List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self,
        List.getD_cons_zero, hv n le_rfl, bin_succ]
      congr 1
      by_cases h2 : 2 ∣ n + 1
      · rw [ite_eq_left (by omega), ite_eq_left h2, hv _ (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right h2]

/-- Table of `b m 0, …, b m N`. -/
def bTab : ℕ → ℕ → List ℕ
  | 0, N => (List.range (N + 1)).map (fun n => if n = 0 then 1 else 0)
  | m + 1, N => (List.range (N + 1)).map (fun n =>
      ∑ i ∈ Finset.range (n + 1), (binTab N).getD i 0 * (bTab m N).getD (n - i) 0)

theorem getD_map_range (N n : ℕ) (f : ℕ → ℕ) (h : n ≤ N) :
    ((List.range (N + 1)).map f).getD n 0 = f n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem bTab_spec (m N n : ℕ) (h : n ≤ N) : (bTab m N).getD n 0 = b m n := by
  induction m generalizing n with
  | zero => rw [bTab, getD_map_range N n _ h, b]
  | succ m ih =>
    rw [bTab, getD_map_range N n _ h, b,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => bin i * b m j)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    rw [(binTab_spec N).2 i (by omega), ih (n - i) (by omega)]

/-- OEIS A018819 (binary partition function), `n = 0, …, 16`. -/
theorem bin_values :
    (List.range 17).map bin = [1, 1, 2, 2, 4, 4, 6, 6, 10, 10, 14, 14, 20, 20, 26, 26, 36] := by
  have : (List.range 17).map bin = (List.range 17).map (fun i => (binTab 16).getD i 0) :=
    List.map_congr_left (fun i hi => ((binTab_spec 16).2 i
      (by have := List.mem_range.1 hi; omega)).symm)
  rw [this]
  decide +kernel

/-- Source, Lemma 4.1: `b_m(0) = 1`. -/
theorem b_zero (m : ℕ) : b m 0 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [b, ih, bin_zero]

/-- Source, Lemma 4.1: `b_m(1) = m`. -/
theorem b_one (m : ℕ) : b m 1 = m := by
  have hb1 : bin 1 = 1 := by rw [bin_succ, bin_zero]; simp
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [b, Finset.Nat.antidiagonal_succ]
    simp [ih, bin_zero, hb1, b_zero]

/-- `b₁₁(n)` for `n = 0, …, 15`, and `b₁₁(12) = 2⁴ · 724 977`. -/
theorem b11_values :
    (List.range 16).map (b 11) = [1, 11, 77, 407, 1804, 6996, 24508, 78980, 237589, 673783,
      1816177, 4681491, 11599632, 27740240, 64256016, 144581712] := by
  have : (List.range 16).map (b 11) = (List.range 16).map (fun i => (bTab 11 15).getD i 0) :=
    List.map_congr_left (fun i hi => (bTab_spec 11 15 i
      (by have := List.mem_range.1 hi; omega)).symm)
  rw [this]
  decide +kernel

theorem b11_12 : b 11 12 = 11599632 := by
  rw [← bTab_spec 11 12 12 le_rfl]
  decide +kernel

/-- The bound `ν₂(b₁₁(n)) ≤ 4` is attained at `n = 12`. -/
theorem padicValNat_b11_12 : padicValNat 2 (b 11 12) = 4 := by
  rw [b11_12, show 11599632 = 2 ^ 4 * 724977 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end MathDB335487
```

### `BinAxioms.lean`

```lean
import BinMain
import BinValues

/-! Endpoint statements and axiom reports. -/

open MathDB335487

#print MathDB335487.bin
#print MathDB335487.b
#print MathDB335487.Conjecture53
#check @MathDB335487.mathdb_335487_refuted
#check @MathDB335487.not_conjecture53
#check @MathDB335487.b11_not_dvd
#check @MathDB335487.family_not_dvd
#check @MathDB335487.family_counterexample
#check @MathDB335487.b11_values
#check @MathDB335487.padicValNat_b11_12
#check @MathDB335487.bin_values
#check @MathDB335487.b_one
#print axioms MathDB335487.mathdb_335487_refuted
#print axioms MathDB335487.not_conjecture53
#print axioms MathDB335487.b11_not_dvd
#print axioms MathDB335487.family_not_dvd
#print axioms MathDB335487.family_counterexample
#print axioms MathDB335487.b11_values
#print axioms MathDB335487.padicValNat_b11_12
#print axioms MathDB335487.bin_values
#print axioms MathDB335487.b_zero
#print axioms MathDB335487.b_one
```
