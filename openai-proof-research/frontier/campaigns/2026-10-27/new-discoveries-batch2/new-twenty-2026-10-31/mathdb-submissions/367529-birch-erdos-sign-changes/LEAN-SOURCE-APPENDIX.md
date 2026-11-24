# Lean source appendix (MathDB 367529)

Modules are listed in import order. Each fenced block is byte-identical to `src/<Module>.lean`.

### `FpqStatement.lean`

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# MathDB 367529: statement

Ding, Liu and Wang, arXiv:2503.11676, Conjecture 3.  `f p q n` is the number of
expressions of `n` as a sum of distinct terms taken from `{p^α q^β : α, β ∈ ℕ}`.
-/

namespace Fpq

/-- the Birch–Erdős set `{p^α q^β : α β ∈ ℕ}` -/
def BE (p q : ℕ) : Set ℕ := {s | ∃ α β : ℕ, s = p ^ α * q ^ β}

open Classical in
/-- `f_{p,q}(n)`: number of finite sets of distinct elements of `BE p q` with sum `n` -/
noncomputable def f (p q n : ℕ) : ℕ :=
  (((Finset.range (n + 1)).filter (· ∈ BE p q)).powerset.filter (fun T => T.sum id = n)).card

/-- The literal statement of Conjecture 3 (both signs occur infinitely often). -/
def Conj3 : Prop :=
  ∀ p q : ℕ, 2 < p → p < q → Nat.Coprime p q →
    (∀ N, ∃ n ≥ N, f p q (n + 1) < f p q n) ∧ (∀ N, ∃ n ≥ N, f p q n < f p q (n + 1))

/-- `0` is not in the set when `p, q ≥ 1`, so counting subsets of `BE ∩ [0,n]` counts
the source's expressions. -/
theorem zero_not_mem_BE (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) : 0 ∉ BE p q := by
  rintro ⟨α, β, h⟩
  have h1 : 0 < p ^ α := pow_pos hp α
  have h2 : 0 < q ^ β := pow_pos hq β
  have := Nat.mul_pos h1 h2
  omega

theorem one_mem_BE (p q : ℕ) : 1 ∈ BE p q := ⟨0, 0, by simp⟩

theorem two_not_mem_BE_3_4 : 2 ∉ BE 3 4 := by
  rintro ⟨α, β, h⟩
  rcases α with _ | α
  · rcases β with _ | β
    · simp at h
    · have : 4 ∣ 2 := ⟨4 ^ β, by rw [h]; ring⟩
      norm_num at this
  · have : 3 ∣ 2 := ⟨3 ^ α * 4 ^ β, by rw [h]; ring⟩
    norm_num at this

open Classical in
theorem filter_BE_3_4_range3 :
    (Finset.range 3).filter (· ∈ BE 3 4) = {1} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hmem⟩
    interval_cases s
    · exact absurd hmem (zero_not_mem_BE 3 4 (by norm_num) (by norm_num))
    · rfl
    · exact absurd hmem two_not_mem_BE_3_4
  · rintro rfl
    exact ⟨by norm_num, one_mem_BE 3 4⟩

open Classical in
theorem filter_BE_3_4_range2 :
    (Finset.range 2).filter (· ∈ BE 3 4) = {1} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hmem⟩
    interval_cases s
    · exact absurd hmem (zero_not_mem_BE 3 4 (by norm_num) (by norm_num))
    · rfl
  · rintro rfl
    exact ⟨by norm_num, one_mem_BE 3 4⟩

open Classical in
theorem filter_BE_3_4_range1 :
    (Finset.range 1).filter (· ∈ BE 3 4) = ∅ := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  intro hs hmem
  interval_cases s
  exact zero_not_mem_BE 3 4 (by norm_num) (by norm_num) hmem

/-- kernel-checked sanity values -/
theorem f_3_4_0 : f 3 4 0 = 1 := by
  unfold f
  rw [filter_BE_3_4_range1]
  decide

theorem f_3_4_1 : f 3 4 1 = 1 := by
  unfold f
  rw [filter_BE_3_4_range2]
  decide

theorem f_3_4_2 : f 3 4 2 = 0 := by
  unfold f
  rw [filter_BE_3_4_range3]
  decide

/-- the first decrease for `(p,q) = (3,4)` -/
theorem f_3_4_decrease : f 3 4 2 < f 3 4 1 := by
  rw [f_3_4_1, f_3_4_2]; norm_num

/-- the hypotheses are satisfiable -/
theorem hyp_nonvacuous : 2 < 3 ∧ 3 < 4 ∧ Nat.Coprime 3 4 := by
  refine ⟨by norm_num, by norm_num, by decide⟩

end Fpq
```

### `FpqCount.lean`

```lean
import FpqStatement
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite truncations of the generating function

`A p q M = BE p q ∩ [0, M]`, `cnt S n` = number of subsets of `S` with sum `n`.
`∏_{s ∈ S} (1 + z^s) = ∑_n cnt S n z^n` and `cnt (A p q M) n = f p q n` for `n ≤ M`.
-/

namespace Fpq

open Finset
open Classical

/-- `BE p q ∩ [0, M]` -/
noncomputable def A (p q M : ℕ) : Finset ℕ := (range (M + 1)).filter (· ∈ BE p q)

/-- number of subsets of `S` with sum `n` -/
def cnt (S : Finset ℕ) (n : ℕ) : ℕ := (S.powerset.filter (fun T => T.sum id = n)).card

theorem f_eq_cnt (p q n : ℕ) : f p q n = cnt (A p q n) n := rfl

theorem mem_A {p q M s : ℕ} : s ∈ A p q M ↔ s ≤ M ∧ s ∈ BE p q := by
  simp only [A, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem A_mono {p q M M' : ℕ} (h : M ≤ M') : A p q M ⊆ A p q M' := by
  intro s hs
  rw [mem_A] at hs ⊢
  exact ⟨hs.1.trans h, hs.2⟩

theorem cnt_A_eq {p q n M : ℕ} (h : n ≤ M) : cnt (A p q M) n = f p q n := by
  rw [f_eq_cnt]
  unfold cnt
  congr 1
  ext T
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hT, hs⟩
    refine ⟨fun t ht => ?_, hs⟩
    have h1 := hT ht
    rw [mem_A] at h1 ⊢
    have h2 : id t ≤ T.sum id := single_le_sum (fun i _ => Nat.zero_le (id i)) ht
    have h3 : t ≤ n := by rw [← hs]; exact h2
    exact ⟨h3, h1.2⟩
  · rintro ⟨hT, hs⟩
    exact ⟨hT.trans (A_mono h), hs⟩

theorem cnt_eq_zero (S : Finset ℕ) {n : ℕ} (h : S.sum id < n) : cnt S n = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro T hT hsum
  have : T.sum id ≤ S.sum id := sum_le_sum_of_subset (f := id) (mem_powerset.1 hT)
  omega

/-- the finite generating identity -/
theorem prod_eq_sum {R : Type*} [CommSemiring R] (S : Finset ℕ) (z : R) (L : ℕ)
    (hL : S.sum id < L) :
    ∏ s ∈ S, (1 + z ^ s) = ∑ n ∈ range L, (cnt S n : R) * z ^ n := by
  rw [prod_one_add]
  have h1 : ∀ T ∈ S.powerset, ∏ i ∈ T, z ^ i = z ^ (T.sum id) := fun T _ => by
    rw [prod_pow_eq_pow_sum]; rfl
  rw [sum_congr rfl h1]
  have hmaps : ∀ T ∈ S.powerset, T.sum id ∈ range L := by
    intro T hT
    have : T.sum id ≤ S.sum id := sum_le_sum_of_subset (f := id) (mem_powerset.1 hT)
    rw [mem_range]; omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro n _
  have h2 : ∀ T ∈ S.powerset.filter (fun T => T.sum id = n), z ^ (T.sum id) = z ^ n :=
    fun T hT => by rw [(mem_filter.1 hT).2]
  rw [sum_congr rfl h2, sum_const, nsmul_eq_mul]
  rfl

/-- multiplication by `1 - z` -/
theorem one_sub_mul_sum {R : Type*} [CommRing R] (c : ℕ → R) (z : R) (L : ℕ) (hc : c L = 0) :
    (1 - z) * ∑ n ∈ range (L + 1), c n * z ^ n =
      ∑ n ∈ range (L + 1), (c n - (if n = 0 then 0 else c (n - 1))) * z ^ n := by
  have h1 : ∑ n ∈ range (L + 1), z * (c n * z ^ n) = ∑ n ∈ range L, c n * z ^ (n + 1) := by
    rw [sum_range_succ, hc]
    simp only [zero_mul, mul_zero, add_zero]
    apply sum_congr rfl
    intro n _
    ring
  have h2 : ∑ n ∈ range (L + 1), (if n = 0 then 0 else c (n - 1)) * z ^ n =
      ∑ n ∈ range L, c n * z ^ (n + 1) := by
    rw [sum_range_succ']
    simp
  rw [sub_mul, one_mul, mul_sum, h1]
  simp only [sub_mul]
  rw [sum_sub_distrib, h2]

/-! ## Structure of `BE p q` -/

theorem pow_mem_BE (p q a : ℕ) : p ^ a ∈ BE p q := ⟨a, 0, by simp⟩

theorem mul_mem_BE (p q a b : ℕ) : p ^ a * q ^ b ∈ BE p q := ⟨a, b, rfl⟩

theorem not_dvd_pow {p q : ℕ} (hq : 2 ≤ q) (hcop : Nat.Coprime p q) (a : ℕ) : ¬ q ∣ p ^ a := by
  intro h
  have : Nat.Coprime q (p ^ a) := (Nat.Coprime.pow_right a hcop.symm)
  have := Nat.Coprime.eq_one_of_dvd this h
  omega

theorem eq_pow_of_mem_BE {p q s : ℕ} (hs : s ∈ BE p q) (hns : ¬ q ∣ s) : ∃ a, s = p ^ a := by
  obtain ⟨α, β, rfl⟩ := hs
  rcases β with _ | β
  · exact ⟨α, by simp⟩
  · exact absurd ⟨p ^ α * q ^ β, by ring⟩ hns

theorem BE_inj_aux {p q : ℕ} (hp : 2 ≤ p) (hcop : Nat.Coprime p q) {a b a' b' : ℕ}
    (h : p ^ a * q ^ b = p ^ a' * q ^ b') (hlt : a < a') : False := by
  have e : p ^ a' = p ^ a * p ^ (a' - a) := by rw [← pow_add]; congr 1; omega
  rw [e, mul_assoc] at h
  have hpa : 0 < p ^ a := pow_pos (by omega) a
  have h2 : q ^ b = p ^ (a' - a) * q ^ b' := Nat.eq_of_mul_eq_mul_left hpa h
  have hd : p ∣ q ^ b := by
    rw [h2]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right b hcop) hd
  omega

theorem BE_inj {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q) {a b a' b' : ℕ}
    (h : p ^ a * q ^ b = p ^ a' * q ^ b') : a = a' ∧ b = b' := by
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact (BE_inj_aux hp hcop h hlt).elim
  · subst heq
    have hpa : 0 < p ^ a := pow_pos (by omega) a
    exact ⟨rfl, Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_left hpa h)⟩
  · exact (BE_inj_aux hp hcop h.symm hgt).elim

/-- the elements of `A p q M` not divisible by `q` are the powers `p^a ≤ M` -/
theorem A_filter_not_dvd {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q) (M : ℕ) :
    (A p q M).filter (fun s => ¬ q ∣ s) =
      ((range (M + 1)).filter (fun a => p ^ a ≤ M)).image (p ^ ·) := by
  ext s
  simp only [mem_filter, mem_image, mem_range, mem_A]
  constructor
  · rintro ⟨⟨hsM, hsBE⟩, hns⟩
    obtain ⟨a, rfl⟩ := eq_pow_of_mem_BE hsBE hns
    have : a < p ^ a := Nat.lt_pow_self (by omega)
    exact ⟨a, ⟨by omega, hsM⟩, rfl⟩
  · rintro ⟨a, ⟨_, haM⟩, rfl⟩
    exact ⟨⟨haM, pow_mem_BE p q a⟩, not_dvd_pow hq hcop a⟩

end Fpq
```

### `FpqRoots.lean`

```lean
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Choice of the root of unity

For coprime `p ≥ 2`, `q ≥ 3` there is `c > 0` such that for every `N` some `ω` with `ω^q = 1`
has `c ≤ |Im ω|` and `∏_{a ≤ N} ‖1 + ω^{p^a}‖ ≥ 1`.
-/

namespace Fpq

open Finset Polynomial Complex

/-- the nontrivial `d`-th roots of unity -/
noncomputable def R (d : ℕ) : Finset ℂ := (nthRootsFinset d (1 : ℂ)).erase 1

theorem mem_R {d : ℕ} (hd : 0 < d) {ξ : ℂ} : ξ ∈ R d ↔ ξ ≠ 1 ∧ ξ ^ d = 1 := by
  simp [R, mem_erase, mem_nthRootsFinset hd]

theorem prod_R_neg_one_sub {d : ℕ} (hd : Odd d) : ∏ ξ ∈ R d, (-1 - ξ) = 1 := by
  have hd0 : 0 < d := hd.pos
  have hζ := Complex.isPrimitiveRoot_exp d (by omega)
  have h := X_pow_sub_one_eq_prod hd0 hζ
  have h2 := congrArg (eval (-1 : ℂ)) h
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at h2
  have h1mem : (1 : ℂ) ∈ nthRootsFinset d (1 : ℂ) := by
    rw [mem_nthRootsFinset hd0]; simp
  rw [← mul_prod_erase _ _ h1mem, hd.neg_one_pow] at h2
  have hne : (-1 - 1 : ℂ) ≠ 0 := by norm_num
  have h3 : (-1 - 1 : ℂ) * ∏ ξ ∈ R d, (-1 - ξ) = (-1 - 1) * 1 := by
    rw [mul_one]; exact h2.symm
  exact mul_left_cancel₀ hne h3

theorem prod_R_norm_one_add {d : ℕ} (hd : Odd d) : ∏ ξ ∈ R d, ‖1 + ξ‖ = 1 := by
  have h : ∀ ξ ∈ R d, ‖1 + ξ‖ = ‖-1 - ξ‖ := fun ξ _ => by
    rw [← norm_neg]; congr 1; ring
  rw [prod_congr rfl h, ← Complex.norm_prod, prod_R_neg_one_sub hd, norm_one]

theorem pow_mul_eq_self {d e e' : ℕ} (he : e * e' % d = 1) {ξ : ℂ} (hξ : ξ ^ d = 1) :
    ξ ^ (e * e') = ξ := by
  rw [← Nat.div_add_mod (e * e') d, pow_add, pow_mul, hξ, one_pow, one_mul, he, pow_one]

/-- `ξ ↦ ξ^e` permutes the nontrivial `d`-th roots when `e` is coprime to `d` -/
theorem prod_R_pow {d e : ℕ} (hd : 1 < d) (he : Nat.Coprime e d) (g : ℂ → ℝ) :
    ∏ ξ ∈ R d, g (ξ ^ e) = ∏ ξ ∈ R d, g ξ := by
  obtain ⟨e', _, he'⟩ := Nat.exists_mul_mod_eq_one_of_coprime he hd
  have hd0 : 0 < d := by omega
  have he'' : e' * e % d = 1 := by rw [mul_comm]; exact he'
  refine prod_nbij' (· ^ e) (· ^ e') ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro ξ hξ
    rw [mem_R hd0] at hξ ⊢
    refine ⟨fun h1 => hξ.1 ?_, by rw [← pow_mul, mul_comm, pow_mul, hξ.2, one_pow]⟩
    rw [← pow_mul_eq_self he' hξ.2, pow_mul, h1, one_pow]
  · intro ξ hξ
    rw [mem_R hd0] at hξ ⊢
    refine ⟨fun h1 => hξ.1 ?_, by rw [← pow_mul, mul_comm, pow_mul, hξ.2, one_pow]⟩
    rw [← pow_mul_eq_self he'' hξ.2, pow_mul, h1, one_pow]
  · intro ξ hξ
    rw [mem_R hd0] at hξ
    rw [← pow_mul, pow_mul_eq_self he' hξ.2]
  · intro ξ hξ
    rw [mem_R hd0] at hξ
    rw [← pow_mul, pow_mul_eq_self he'' hξ.2]

theorem R_nonempty {d : ℕ} (hd : 1 < d) : (R d).Nonempty := by
  have hζ := Complex.isPrimitiveRoot_exp d (by omega)
  refine ⟨_, (mem_R (by omega)).2 ⟨hζ.ne_one hd, hζ.pow_eq_one⟩⟩

theorem exists_good_R {d p : ℕ} (hd : Odd d) (hd1 : 1 < d) (hcop : Nat.Coprime p d) (N : ℕ) :
    ∃ ξ ∈ R d, 1 ≤ ∏ a ∈ range (N + 1), ‖1 + ξ ^ (p ^ a)‖ := by
  have hprod : ∏ ξ ∈ R d, ∏ a ∈ range (N + 1), ‖1 + ξ ^ (p ^ a)‖ = 1 := by
    rw [prod_comm]
    apply prod_eq_one
    intro a _
    rw [prod_R_pow hd1 (Nat.Coprime.pow_left a hcop) (fun ξ => ‖1 + ξ‖)]
    exact prod_R_norm_one_add hd
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨ξ0, hξ0⟩ := R_nonempty hd1
  have hle : ∏ ξ ∈ (R d).erase ξ0, ∏ a ∈ range (N + 1), ‖1 + ξ ^ (p ^ a)‖ ≤ 1 :=
    prod_le_one₀ (fun ξ _ => prod_nonneg (fun _ _ => norm_nonneg _))
      (fun ξ hξ => (hcon ξ (mem_of_mem_erase hξ)).le)
  have hnn : 0 ≤ ∏ ξ ∈ (R d).erase ξ0, ∏ a ∈ range (N + 1), ‖1 + ξ ^ (p ^ a)‖ :=
    prod_nonneg (fun ξ _ => prod_nonneg (fun _ _ => norm_nonneg _))
  rw [← mul_prod_erase _ _ hξ0] at hprod
  have h0 := hcon ξ0 hξ0
  have h0' : 0 ≤ ∏ a ∈ range (N + 1), ‖1 + ξ0 ^ (p ^ a)‖ := prod_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem im_ne_zero_of_mem_R {d : ℕ} (hd : Odd d) {ξ : ℂ} (hξ : ξ ∈ R d) : ξ.im ≠ 0 := by
  rw [mem_R hd.pos] at hξ
  intro him
  have hξr : ξ = (ξ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have h1 : ((ξ.re ^ d : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [ofReal_pow, ← hξr, hξ.2, ofReal_one]
  have h2 : ξ.re ^ d = (1 : ℝ) ^ d := by rw [one_pow]; exact_mod_cast h1
  have h3 : ξ.re = 1 := hd.pow_inj.1 h2
  exact hξ.1 (by rw [hξr, h3, ofReal_one])

theorem I_pow_odd_re {n : ℕ} (hn : Odd n) : (I ^ n).re = 0 := by
  obtain ⟨t, rfl⟩ := hn
  rw [pow_add, pow_mul, I_sq, pow_one]
  rcases neg_one_pow_eq_or ℂ t with h | h <;> rw [h] <;> simp

/-- the choice of `ω` -/
theorem exists_roots {p q : ℕ} (hq : 3 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ ω : ℂ, ω ^ q = 1 ∧ c ≤ |ω.im| ∧
      1 ≤ ∏ a ∈ range (N + 1), ‖1 + ω ^ (p ^ a)‖ := by
  obtain ⟨v, o, hodd, hqeq⟩ := Nat.exists_eq_two_pow_mul_odd (n := q) (by omega)
  by_cases ho : 1 < o
  · -- an odd divisor `o ≥ 3` of `q`
    have hcop' : Nat.Coprime p o := Nat.Coprime.coprime_dvd_right ⟨2 ^ v, by rw [hqeq]; ring⟩ hcop
    obtain ⟨ξ0, hξ0, hmin⟩ := (R o).exists_min_image (fun ξ => |ξ.im|) (R_nonempty ho)
    refine ⟨|ξ0.im|, abs_pos.2 (im_ne_zero_of_mem_R hodd hξ0), fun N => ?_⟩
    obtain ⟨ξ, hξ, hge⟩ := exists_good_R hodd ho hcop' N
    refine ⟨ξ, ?_, hmin ξ hξ, hge⟩
    rw [mem_R hodd.pos] at hξ
    rw [hqeq, mul_comm, pow_mul, hξ.2, one_pow]
  · -- `q` is a power of two, `q ≥ 4`
    have ho1 : o = 1 := by obtain ⟨t, rfl⟩ := hodd; omega
    rw [ho1, mul_one] at hqeq
    have hv : 2 ≤ v := by
      by_contra hv
      interval_cases v <;> omega
    have hpodd : Odd p := by
      rw [Nat.odd_iff]
      by_contra hp2
      have h2p : 2 ∣ p := by omega
      have h2q : 2 ∣ q := ⟨2 ^ (v - 1), by rw [hqeq, ← pow_succ']; congr 1; omega⟩
      have h2g : 2 ∣ Nat.gcd p q := Nat.dvd_gcd h2p h2q
      rw [Nat.Coprime.gcd_eq_one hcop] at h2g
      omega
    refine ⟨1, one_pos, fun N => ⟨I, ?_, by simp, ?_⟩⟩
    · have : q = 4 * 2 ^ (v - 2) := by
        rw [hqeq, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      rw [this, pow_mul, I_pow_four, one_pow]
    · apply one_le_prod₀
      intro a _
      have hre : (1 + I ^ (p ^ a)).re = 1 := by
        rw [add_re, I_pow_odd_re (hpodd.pow), one_re, add_zero]
      have := abs_re_le_norm (1 + I ^ (p ^ a))
      rw [hre, abs_one] at this
      exact this

end Fpq
```

### `FpqAnalysis.lean`

```lean
import FpqCount
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Elementary estimates

Step 4 of the proof, Bernoulli bounds for `x = 1 - 1/m`, the finite Pringsheim bound,
and the tail estimates for the finite generating products.
-/

namespace Fpq

open Finset Complex

/-- Step 4: `|1 + ζ y| ≥ (1+y)/2 · |1 + ζ|` for `|ζ| = 1`, `0 ≤ y ≤ 1`. -/
theorem step4 (ζ : ℂ) (hζ : ‖ζ‖ = 1) (y : ℝ) (hy0 : 0 ≤ y) :
    (1 + y) / 2 * ‖1 + ζ‖ ≤ ‖1 + ζ * y‖ := by
  have hn : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
    have h := Complex.sq_norm ζ
    rw [hζ, Complex.normSq_apply] at h
    linarith
  have hsq1 : ‖1 + ζ‖ ^ 2 = (1 + ζ.re) * (1 + ζ.re) + ζ.im * ζ.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp
  have hsq2 : ‖1 + ζ * y‖ ^ 2 = (1 + ζ.re * y) * (1 + ζ.re * y) + (ζ.im * y) * (ζ.im * y) := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp
  have hre : ζ.re ≤ 1 := by nlinarith [sq_nonneg ζ.im, sq_nonneg (ζ.re - 1)]
  have key : ((1 + y) / 2 * ‖1 + ζ‖) ^ 2 ≤ ‖1 + ζ * y‖ ^ 2 := by
    rw [mul_pow, hsq1, hsq2]
    nlinarith [mul_nonneg (sub_nonneg.2 hre) (sq_nonneg (1 - y))]
  have h0 : 0 ≤ (1 + y) / 2 * ‖1 + ζ‖ := by positivity
  exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).1 key

/-- the crude factor bound used for large exponents -/
theorem tail_factor (ζ : ℂ) (hζ : ‖ζ‖ = 1) (y : ℝ) (hy0 : 0 ≤ y) :
    (1 - 2 * y) * (1 + y) ≤ ‖1 + ζ * y‖ := by
  have h1 : ‖(1 : ℂ)‖ - ‖-(ζ * y)‖ ≤ ‖(1 : ℂ) - -(ζ * y)‖ := norm_sub_norm_le _ _
  rw [norm_neg, norm_mul, hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0,
    norm_one, sub_neg_eq_add] at h1
  nlinarith

/-- `∏ (1 - u_i) ≥ 1 - ∑ u_i` for `u_i ∈ [0,1]` -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) : 1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => hu i (mem_insert_of_mem hi))
    have hua := hu a (mem_insert_self a s)
    have hP : 0 ≤ ∏ i ∈ s, (1 - u i) :=
      prod_nonneg (fun i hi => by have := hu i (mem_insert_of_mem hi); linarith)
    have hS : 0 ≤ ∑ i ∈ s, u i := sum_nonneg (fun i hi => (hu i (mem_insert_of_mem hi)).1)
    nlinarith

/-! ## Bernoulli bounds for `x = 1 - 1/m` -/

theorem pow_m_le_half (m : ℕ) (hm : 1 ≤ m) : (1 - 1 / (m : ℝ)) ^ m ≤ 1 / 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hinv : 0 < 1 / (m : ℝ) := by positivity
  have hinv1 : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hm'
  have h1 : 2 ≤ (1 + 1 / (m : ℝ)) ^ m := by
    have := one_add_mul_le_pow (a := 1 / (m : ℝ)) (by linarith) m
    have e : (m : ℝ) * (1 / m) = 1 := by field_simp
    linarith
  have h2 : ((1 - 1 / (m : ℝ)) * (1 + 1 / (m : ℝ))) ^ m ≤ 1 := by
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  rw [mul_pow] at h2
  have h3 : 0 ≤ (1 - 1 / (m : ℝ)) ^ m := pow_nonneg (by linarith) m
  nlinarith

theorem one_sub_le_pow (m s : ℕ) (hm : 1 ≤ m) :
    1 - (s : ℝ) / m ≤ (1 - 1 / (m : ℝ)) ^ s := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hinv1 : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hm'
  have := one_add_mul_le_pow (a := -(1 / (m : ℝ))) (by linarith) s
  have e : (s : ℝ) * -(1 / (m : ℝ)) = -((s : ℝ) / m) := by ring
  rw [e, ← sub_eq_add_neg, ← sub_eq_add_neg] at this
  exact this

/-! ## The finite Pringsheim bound -/

/-- If the coefficients `c n` are nondecreasing on `[n0, M]`, then
`‖(1-z) ∑ c_n z^n‖ ≤ (1-x) ∑ c_n x^n + 2 K + 2 T` with `x = ‖z‖`, `K` a sum over `n ≤ n0`
and `T` the tail `∑_{n ≥ M} c_n x^n`. -/
theorem pringsheim (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (L : ℕ) (hcL : c L = 0) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (z : ℂ) (hz : ‖z‖ = x) (n0 M : ℕ)
    (hmono : ∀ n, n0 ≤ n → n < M → c n ≤ c (n + 1)) :
    ‖(1 - z) * ∑ n ∈ range (L + 1), (c n : ℂ) * z ^ n‖ ≤
      (1 - x) * ∑ n ∈ range (L + 1), c n * x ^ n
        + 2 * ∑ n ∈ range (n0 + 1), (if n = 0 then 0 else c (n - 1))
        + 2 * ∑ n ∈ range L, (if M ≤ n then c n * x ^ n else 0) := by
  set cp : ℕ → ℝ := fun n => if n = 0 then 0 else c (n - 1) with hcp
  set d : ℕ → ℝ := fun n => c n - cp n with hd
  have hcpnn : ∀ n, 0 ≤ cp n := fun n => by
    simp only [hcp]; split_ifs
    · exact le_rfl
    · exact hc _
  -- complex identity
  have hC := one_sub_mul_sum (fun n => ((c n : ℝ) : ℂ)) z L (by simp [hcL])
  have hcoef : ∀ n, (((c n : ℝ) : ℂ) - (if n = 0 then 0 else ((c (n - 1) : ℝ) : ℂ))) =
      ((d n : ℝ) : ℂ) := fun n => by
    simp only [hd, hcp]; split_ifs <;> simp
  simp only [hcoef] at hC
  rw [hC]
  have hR := one_sub_mul_sum c x L hcL
  have hR' : (1 - x) * ∑ n ∈ range (L + 1), c n * x ^ n = ∑ n ∈ range (L + 1), d n * x ^ n := by
    rw [hR]
  rw [hR']
  refine (norm_sum_le _ _).trans ?_
  have hnorm : ∀ n, ‖((d n : ℝ) : ℂ) * z ^ n‖ = |d n| * x ^ n := fun n => by
    rw [norm_mul, norm_pow, hz, Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm]
  -- pointwise bound
  have hpt : ∀ n, |d n| * x ^ n ≤ d n * x ^ n +
      ((if n ≤ n0 then 2 * cp n else 0) + (if M < n then 2 * cp n * x ^ n else 0)) := by
    intro n
    have hxn0 : 0 ≤ x ^ n := pow_nonneg hx0 n
    have hxn1 : x ^ n ≤ 1 := pow_le_one₀ hx0 hx1
    have hdl : -cp n ≤ d n := by simp only [hd]; linarith [hc n]
    have hgen : |d n| - d n ≤ 2 * cp n := by
      rcases le_or_gt 0 (d n) with h | h
      · rw [abs_of_nonneg h]; linarith [hcpnn n]
      · rw [abs_of_neg h]; linarith
    have habs : 0 ≤ |d n| - d n := by linarith [le_abs_self (d n)]
    by_cases h1 : n ≤ n0
    · rw [ite_eq_left h1]
      have hB : 0 ≤ (if M < n then 2 * cp n * x ^ n else 0) := by
        split_ifs
        · exact mul_nonneg (by linarith [hcpnn n]) hxn0
        · exact le_rfl
      nlinarith
    · by_cases h2 : M < n
      · rw [ite_eq_right h1, ite_eq_left h2]
        nlinarith
      · rw [ite_eq_right h1, ite_eq_right h2]
        have hn1 : 1 ≤ n := by omega
        have hdn : 0 ≤ d n := by
          simp only [hd, hcp, ite_eq_right (show n ≠ 0 by omega)]
          have := hmono (n - 1) (by omega) (by omega)
          rw [show n - 1 + 1 = n by omega] at this
          linarith
        rw [abs_of_nonneg hdn]
        linarith
  refine (sum_le_sum (fun n _ => hpt n)).trans ?_
  rw [sum_add_distrib, sum_add_distrib, add_assoc]
  refine add_le_add le_rfl (add_le_add ?_ ?_)
  · -- the initial segment
    rw [← sum_filter, mul_sum]
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [mem_filter] at hn
      rw [mem_range]; omega
    · intro n _ _
      linarith [hcpnn n]
  · -- the tail
    rw [sum_range_succ', mul_sum]
    simp only [show ¬ (M < 0) from by omega, ite_false, add_zero]
    apply sum_le_sum
    intro n _
    simp only [hcp, Nat.add_sub_cancel, ite_eq_right (Nat.succ_ne_zero n)]
    by_cases h : M < n + 1
    · rw [ite_eq_left h, ite_eq_left (by omega : M ≤ n)]
      have : x ^ (n + 1) ≤ x ^ n := pow_le_pow_of_le_one hx0 hx1 (by omega)
      nlinarith [hc n]
    · rw [ite_eq_right h, ite_eq_right (by omega : ¬ M ≤ n)]
      simp

/-- the tail is small: `∑_{n ≥ M} c_n (y^2)^n ≤ y^M ∑ c_n y^n` -/
theorem tail_le (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (L M : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∑ n ∈ range L, (if M ≤ n then c n * (y ^ 2) ^ n else 0) ≤
      y ^ M * ∑ n ∈ range L, c n * y ^ n := by
  rw [mul_sum]
  apply sum_le_sum
  intro n _
  have h0 : 0 ≤ c n * y ^ n := mul_nonneg (hc n) (pow_nonneg hy0 n)
  split_ifs with h
  · have : y ^ n ≤ y ^ M := pow_le_pow_of_le_one hy0 hy1 h
    rw [← pow_mul, show 2 * n = n + n by ring, pow_add]
    nlinarith [pow_nonneg hy0 n]
  · exact mul_nonneg (pow_nonneg hy0 M) h0

/-- bounded coefficients give `∑ c_n x^n ≤ B/(1-x) + tail` -/
theorem sum_le_of_bdd (c : ℕ → ℝ) (L : ℕ) (x : ℝ) (hx0 : 0 ≤ x)
    (hx1 : x < 1) (M : ℕ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ n, n < M → c n ≤ B) :
    ∑ n ∈ range L, c n * x ^ n ≤
      B / (1 - x) + ∑ n ∈ range L, (if M ≤ n then c n * x ^ n else 0) := by
  have hgeom : ∑ n ∈ range L, x ^ n ≤ 1 / (1 - x) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) hx0 hx1
    rwa [← range_eq_Ico, pow_zero] at this
  have h1 : ∑ n ∈ range L, c n * x ^ n ≤
      ∑ n ∈ range L, (B * x ^ n + (if M ≤ n then c n * x ^ n else 0)) := by
    apply sum_le_sum
    intro n _
    have hxn : 0 ≤ x ^ n := pow_nonneg hx0 n
    split_ifs with h
    · nlinarith
    · have := hB n (by omega)
      nlinarith
  rw [sum_add_distrib, ← mul_sum] at h1
  have h2 : B * ∑ n ∈ range L, x ^ n ≤ B / (1 - x) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hgeom hB0
  linarith

/-- uniform bound for the finite products: `∏_{s ∈ S} (1 + y^s) ≤ exp (1/(1-y))` -/
theorem prod_le_exp (S : Finset ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∏ s ∈ S, (1 + y ^ s) ≤ Real.exp (1 / (1 - y)) := by
  set L := S.sup id + 1
  have hS : S ⊆ range L := by
    intro s hs
    rw [mem_range]
    have : id s ≤ S.sup id := le_sup hs
    simp only [id] at this
    omega
  have h1 : ∏ s ∈ S, (1 + y ^ s) ≤ ∏ s ∈ S, Real.exp (y ^ s) :=
    prod_le_prod₀ (fun s _ => by positivity)
      (fun s _ => by have := Real.add_one_le_exp (y ^ s); linarith)
  rw [← Real.exp_sum] at h1
  refine h1.trans (Real.exp_le_exp.2 ?_)
  have h2 : ∑ s ∈ S, y ^ s ≤ ∑ s ∈ range L, y ^ s :=
    sum_le_sum_of_subset_of_nonneg hS (fun s _ _ => pow_nonneg hy0 s)
  have h3 := geom_sum_Ico_le_of_lt_one (m := 0) (n := L) hy0 hy1
  rw [← range_eq_Ico, pow_zero] at h3
  linarith

/-- `C b^k (2/3)^{k^2} → 0` -/
theorem small_eventually (C b ε : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ k0 : ℕ, ∀ k ≥ k0, C * b ^ k * (2 / 3 : ℝ) ^ (k * k) < ε := by
  obtain ⟨k1, hk1⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (2 * (b + 1)) by positivity)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  obtain ⟨k2, hk2⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (C + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨max k1 k2, fun k hk => ?_⟩
  have hk1' : k1 ≤ k := le_of_max_le_left hk
  have hk2' : k2 ≤ k := le_of_max_le_right hk
  have e : b ^ k * (2 / 3 : ℝ) ^ (k * k) = (b * (2 / 3 : ℝ) ^ k) ^ k := by
    rw [mul_pow, ← pow_mul, mul_comm k k]
  have hbase0 : 0 ≤ b * (2 / 3 : ℝ) ^ k := by positivity
  have hbase : b * (2 / 3 : ℝ) ^ k ≤ 1 / 2 := by
    have h23 : (2 / 3 : ℝ) ^ k ≤ (2 / 3) ^ k1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk1'
    have h23' : (b + 1) * (2 / 3 : ℝ) ^ k1 < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (b + 1))] at hk1
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have : b * (2 / 3 : ℝ) ^ k ≤ (b + 1) * (2 / 3 : ℝ) ^ k1 := by
      have h0 : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
      nlinarith
    linarith
  have h3 : (b * (2 / 3 : ℝ) ^ k) ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ hbase0 hbase k
  have h4 : (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ k2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk2'
  have h5 : (b * (2 / 3 : ℝ) ^ k) ^ k < ε / (C + 1) := by linarith
  have h6 : (C + 1) * (b * (2 / 3 : ℝ) ^ k) ^ k < ε := by
    rwa [lt_div_iff₀ (by positivity), mul_comm] at h5
  have h7 : 0 ≤ (b * (2 / 3 : ℝ) ^ k) ^ k := by positivity
  rw [mul_assoc, e]
  nlinarith

end Fpq
```

### `FpqRatio.lean`

```lean
import FpqAnalysis
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The twisted product and the growth of the finite product

For `ω^q = 1`, `‖∏_{s ∈ A_M} (1 + (ωx)^s)‖ ≥ 2^{-(N+2)} ∏_{s ∈ A_M} (1 + x^s)`;
and `∏_{s ∈ A_M} (1 + x^s) ≥ (3/2)^{k^2}` when `x^s ≥ 1/2` for `s ≤ p^{2qk}`.
-/

namespace Fpq

open Finset Complex
open Classical

theorem le_pow_sub (p : ℕ) (hp : 3 ≤ p) : ∀ j : ℕ, 1 ≤ j → j + 2 ≤ p ^ j := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp; omega
    · have := ih h
      rw [pow_succ]
      nlinarith

/-- `x^{p^a} ≤ (1/2)^{a-N+2}` for `a > N` when `x^{p^N} ≤ 1/2` -/
theorem x_pow_tail {p N a : ℕ} (hp : 3 ≤ p) (hNa : N < a) {x : ℝ} (hx0 : 0 ≤ x)
    (hxN : x ^ (p ^ N) ≤ 1 / 2) : x ^ (p ^ a) ≤ (1 / 2 : ℝ) ^ (a - N + 2) := by
  have e : p ^ a = p ^ N * p ^ (a - N) := by rw [← pow_add]; congr 1; omega
  rw [e, pow_mul]
  have h1 : (x ^ p ^ N) ^ p ^ (a - N) ≤ (1 / 2 : ℝ) ^ p ^ (a - N) :=
    pow_le_pow_left₀ (pow_nonneg hx0 _) hxN _
  have h2 : (1 / 2 : ℝ) ^ p ^ (a - N) ≤ (1 / 2 : ℝ) ^ (a - N + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_pow_sub p hp (a - N) (by omega))
  exact h1.trans h2

theorem tail_sum_le {p N M : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx0 : 0 ≤ x)
    (hxN : x ^ (p ^ N) ≤ 1 / 2) (B : Finset ℕ) (hB : ∀ a ∈ B, N < a ∧ a ≤ M) :
    ∑ a ∈ B, 2 * x ^ (p ^ a) ≤ 1 / 2 := by
  have h1 : ∑ a ∈ B, 2 * x ^ (p ^ a) ≤ ∑ a ∈ B, 2 * (1 / 2 : ℝ) ^ (a - N + 2) :=
    sum_le_sum (fun a ha => by
      have := x_pow_tail hp (hB a ha).1 hx0 hxN; linarith)
  have h2 : ∑ a ∈ B, 2 * (1 / 2 : ℝ) ^ (a - N + 2) ≤
      ∑ a ∈ Ico (N + 1) (M + 1), 2 * (1 / 2 : ℝ) ^ (a - N + 2) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      have := hB a ha
      rw [mem_Ico]; omega
    · intro _ _ _; positivity
  have h3 : ∑ a ∈ Ico (N + 1) (M + 1), 2 * (1 / 2 : ℝ) ^ (a - N + 2) =
      ∑ j ∈ range (M + 1 - (N + 1)), (1 / 4 : ℝ) * (1 / 2) ^ j := by
    rw [sum_Ico_eq_sum_range]
    apply sum_congr rfl
    intro j _
    rw [show N + 1 + j - N + 2 = j + 3 by omega, pow_add]
    norm_num
    ring
  have h4 : ∑ j ∈ range (M + 1 - (N + 1)), (1 / 4 : ℝ) * (1 / 2) ^ j ≤ 1 / 2 := by
    rw [← mul_sum]
    have := sum_geometric_two_le (M + 1 - (N + 1))
    linarith
  linarith

/-- the twisted finite product is at least `2^{-(N+2)}` times the untwisted one -/
theorem twisted_ge {p q N M : ℕ} (hp : 3 ≤ p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q)
    (hNM : p ^ N ≤ M) {ω : ℂ} (hωq : ω ^ q = 1)
    (hω : 1 ≤ ∏ a ∈ range (N + 1), ‖1 + ω ^ (p ^ a)‖) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxN : x ^ (p ^ N) ≤ 1 / 2) :
    1 / 2 ^ (N + 2) * ∏ s ∈ A p q M, (1 + x ^ s) ≤
      ‖∏ s ∈ A p q M, (1 + (ω * x) ^ s)‖ := by
  have hp2 : 2 ≤ p := by omega
  have hωn : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_one hωq (by omega)
  set h : ℕ → ℝ := fun s =>
    if q ∣ s then 1 else if s ≤ p ^ N then ‖1 + ω ^ s‖ / 2 else 1 - 2 * x ^ s with hh
  have hpow : ∀ s : ℕ, (ω * x) ^ s = ω ^ s * ((x ^ s : ℝ) : ℂ) := fun s => by
    rw [mul_pow, ofReal_pow]
  have hxs0 : ∀ s : ℕ, 0 ≤ x ^ s := fun s => pow_nonneg hx0 s
  have hxs1 : ∀ s : ℕ, x ^ s ≤ 1 := fun s => pow_le_one₀ hx0 hx1
  -- pointwise bounds
  have hpt : ∀ s ∈ A p q M, 0 ≤ h s ∧ h s * (1 + x ^ s) ≤ ‖1 + (ω * x) ^ s‖ := by
    intro s hs
    have hζ : ‖ω ^ s‖ = 1 := by rw [norm_pow, hωn, one_pow]
    rw [hpow]
    by_cases h1 : q ∣ s
    · have hω1 : ω ^ s = 1 := by
        obtain ⟨t, rfl⟩ := h1; rw [pow_mul, hωq, one_pow]
      simp only [hh, ite_eq_left h1, one_mul, hω1]
      refine ⟨zero_le_one, ?_⟩
      rw [show (1 : ℂ) + ((x ^ s : ℝ) : ℂ) = ((1 + x ^ s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hxs0 s])]
    · by_cases h2 : s ≤ p ^ N
      · simp only [hh, ite_eq_right h1, ite_eq_left h2]
        refine ⟨by positivity, ?_⟩
        have := step4 (ω ^ s) hζ (x ^ s) (hxs0 s)
        linarith
      · simp only [hh, ite_eq_right h1, ite_eq_right h2]
        obtain ⟨a, rfl⟩ := eq_pow_of_mem_BE (mem_A.1 hs).2 h1
        have hNa : N < a := by
          by_contra hc
          exact h2 (Nat.pow_le_pow_right (by omega) (by omega))
        have hsmall : x ^ (p ^ a) ≤ 1 / 2 := by
          have : x ^ (p ^ a) ≤ x ^ (p ^ N) :=
            pow_le_pow_of_le_one hx0 hx1 (Nat.pow_le_pow_right (by omega) hNa.le)
          linarith
        exact ⟨by linarith, tail_factor (ω ^ p ^ a) hζ (x ^ p ^ a) (hxs0 _)⟩
  rw [Complex.norm_prod]
  have hstep : ∏ s ∈ A p q M, (h s * (1 + x ^ s)) ≤ ∏ s ∈ A p q M, ‖1 + (ω * x) ^ s‖ :=
    prod_le_prod₀ (fun s hs => mul_nonneg (hpt s hs).1 (by linarith [hxs0 s]))
      (fun s hs => (hpt s hs).2)
  rw [prod_mul_distrib] at hstep
  refine le_trans ?_ hstep
  have hP0 : 0 ≤ ∏ s ∈ A p q M, (1 + x ^ s) := prod_nonneg (fun s _ => by linarith [hxs0 s])
  apply mul_le_mul_of_nonneg_right _ hP0
  -- the product of the `h s`
  have hfil : ∏ s ∈ A p q M, h s = ∏ s ∈ (A p q M).filter (fun s => ¬ q ∣ s), h s := by
    rw [prod_filter]
    apply prod_congr rfl
    intro s _
    by_cases h1 : q ∣ s
    · simp [hh, h1]
    · simp [h1]
  rw [hfil, A_filter_not_dvd hp2 hq hcop M,
    prod_image (fun a _ b _ hab => Nat.pow_right_injective hp2 hab)]
  set B := (range (M + 1)).filter (fun a => p ^ a ≤ M) with hB
  rw [← prod_filter_mul_prod_filter_not B (fun a => a ≤ N)]
  have hB1 : B.filter (fun a => a ≤ N) = range (N + 1) := by
    ext a
    simp only [hB, mem_filter, mem_range]
    constructor
    · rintro ⟨_, h⟩; omega
    · intro ha
      have h1 : p ^ a ≤ M := (Nat.pow_le_pow_right (by omega) (by omega)).trans hNM
      have h2 : a < p ^ a := Nat.lt_pow_self (by omega)
      exact ⟨⟨by omega, h1⟩, by omega⟩
  rw [hB1]
  -- the first `N+1` factors
  have hfirst : ∏ a ∈ range (N + 1), h (p ^ a) = (∏ a ∈ range (N + 1), ‖1 + ω ^ (p ^ a)‖) /
      2 ^ (N + 1) := by
    have hc : ∏ a ∈ range (N + 1), h (p ^ a) = ∏ a ∈ range (N + 1), (‖1 + ω ^ (p ^ a)‖ / 2) := by
      apply prod_congr rfl
      intro a ha
      have hle : p ^ a ≤ p ^ N := Nat.pow_le_pow_right (by omega) (by rw [mem_range] at ha; omega)
      simp only [hh, ite_eq_right (not_dvd_pow hq hcop a), ite_eq_left hle]
    rw [hc, prod_div_distrib, prod_const, card_range]
  have hrest : ∏ a ∈ B.filter (fun a => ¬ a ≤ N), h (p ^ a) =
      ∏ a ∈ B.filter (fun a => ¬ a ≤ N), (1 - 2 * x ^ (p ^ a)) := by
    apply prod_congr rfl
    intro a ha
    rw [mem_filter] at ha
    have hlt : ¬ p ^ a ≤ p ^ N := by
      intro hc
      exact ha.2 ((Nat.pow_le_pow_iff_right (by omega)).1 hc)
    simp only [hh, ite_eq_right (not_dvd_pow hq hcop a), ite_eq_right hlt]
  rw [hfirst, hrest]
  have hBmem : ∀ a ∈ B.filter (fun a => ¬ a ≤ N), N < a ∧ a ≤ M := by
    intro a ha
    simp only [hB, mem_filter, mem_range] at ha
    omega
  have hsum := tail_sum_le hp hx0 hxN _ hBmem
  have hprod := one_sub_sum_le_prod (B.filter (fun a => ¬ a ≤ N)) (fun a => 2 * x ^ (p ^ a))
    (fun a ha => by
      have := x_pow_tail hp (hBmem a ha).1 hx0 hxN
      have h8 : (1 / 2 : ℝ) ^ (a - N + 2) ≤ (1 / 2) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      constructor
      · positivity
      · nlinarith)
  have hfirst' : 1 / 2 ^ (N + 1) ≤ (∏ a ∈ range (N + 1), ‖1 + ω ^ (p ^ a)‖) / 2 ^ (N + 1) :=
    div_le_div_of_nonneg_right hω (by positivity)
  have e : (1 : ℝ) / 2 ^ (N + 2) = 1 / 2 ^ (N + 1) * (1 / 2) := by
    rw [pow_succ]; field_simp
  rw [e]
  exact mul_le_mul hfirst' (by linarith) (by norm_num) (by positivity)

/-- growth of the finite product -/
theorem prod_ge_growth {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hcop : Nat.Coprime p q)
    (k M : ℕ) (hM : p ^ (2 * q * k) ≤ M) {x : ℝ} (hx0 : 0 ≤ x)
    (hxs : ∀ s : ℕ, s ≤ p ^ (2 * q * k) → 1 / 2 ≤ x ^ s) :
    (3 / 2 : ℝ) ^ (k * k) ≤ ∏ s ∈ A p q M, (1 + x ^ s) := by
  set A' := (range (q * k) ×ˢ range k).image (fun ab : ℕ × ℕ => p ^ ab.1 * q ^ ab.2) with hA'
  have hqp : q ≤ p ^ q := (Nat.lt_pow_self (by omega)).le
  have hbound : ∀ a b : ℕ, a < q * k → b < k → p ^ a * q ^ b ≤ p ^ (2 * q * k) := by
    intro a b ha hb
    have h1 : q ^ b ≤ p ^ (q * b) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hqp b
    have h2 : p ^ a * q ^ b ≤ p ^ a * p ^ (q * b) := Nat.mul_le_mul_left _ h1
    rw [← pow_add] at h2
    refine h2.trans (Nat.pow_le_pow_right (by omega) ?_)
    have : q * b + q ≤ q * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left q hb
    nlinarith
  have hsub : A' ⊆ A p q M := by
    intro s hs
    simp only [hA', mem_image, mem_product, mem_range] at hs
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hs
    rw [mem_A]
    exact ⟨(hbound a b ha hb).trans hM, mul_mem_BE p q a b⟩
  have hcard : A'.card = q * k * k := by
    rw [hA', card_image_of_injOn, card_product, card_range, card_range]
    rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ hab
    have := BE_inj hp hq hcop hab
    simp only [Prod.mk.injEq]
    exact this
  have hxs0 : ∀ s : ℕ, 0 ≤ x ^ s := fun s => pow_nonneg hx0 s
  have h1 : ∏ s ∈ A', (1 + x ^ s) ≤ ∏ s ∈ A p q M, (1 + x ^ s) :=
    prod_le_prod_of_subset_of_one_le₀ hsub (fun s _ => by linarith [hxs0 s])
      (fun s _ _ => by linarith [hxs0 s])
  have h2 : ∏ s ∈ A', (3 / 2 : ℝ) ≤ ∏ s ∈ A', (1 + x ^ s) := by
    apply prod_le_prod₀ (fun _ _ => by norm_num)
    intro s hs
    simp only [hA', mem_image, mem_product, mem_range] at hs
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hs
    have := hxs _ (hbound a b ha hb)
    linarith
  rw [prod_const, hcard] at h2
  have h3 : (3 / 2 : ℝ) ^ (k * k) ≤ (3 / 2 : ℝ) ^ (q * k * k) := by
    apply pow_le_pow_right₀ (by norm_num)
    have : k ≤ q * k := Nat.le_mul_of_pos_left k (by omega)
    exact Nat.mul_le_mul_right k this
  linarith

end Fpq
```

### `FpqMain.lean`

```lean
import FpqRatio
import FpqRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# MathDB 367529: Ding–Liu–Wang Conjecture 3

For coprime `q > p > 2`, `f p q (n+1) < f p q n` for infinitely many `n` and
`f p q n < f p q (n+1)` for infinitely many `n`.
-/

namespace Fpq

open Finset Complex
open Classical

theorem x_bounds (m : ℕ) (hm : 2 ≤ m) :
    1 / 2 ≤ 1 - 1 / (m : ℝ) ∧ 1 - 1 / (m : ℝ) < 1 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 1 / (m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm'
  have h2 : 0 < 1 / (m : ℝ) := by positivity
  constructor <;> linarith

theorem x_pow_ge_half (m s : ℕ) (hm : 1 ≤ m) (hs : 2 * s ≤ m) :
    1 / 2 ≤ (1 - 1 / (m : ℝ)) ^ s := by
  have h := one_sub_le_pow m s hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs' : (2 : ℝ) * s ≤ m := by exact_mod_cast hs
  have : (s : ℝ) / m ≤ 1 / 2 := by
    rw [div_le_iff₀ hm']; linarith
  linarith

/-- for fixed `x < 1` the tails of the finite generating products are uniformly small -/
theorem exists_M (p q : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (M0 : ℕ) :
    ∃ M, M0 ≤ M ∧ ∀ L : ℕ,
      ∑ n ∈ range L, (if M ≤ n then (cnt (A p q M) n : ℝ) * x ^ n else 0) ≤ 1 / 4 := by
  set y := Real.sqrt x with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg x
  have hy2 : y ^ 2 = x := Real.sq_sqrt hx0
  have hy1 : y < 1 := by
    rw [hy, Real.sqrt_lt' one_pos]; simpa using hx1
  set E := Real.exp (1 / (1 - y)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (4 * E) by positivity) hy1
  refine ⟨max M0 n1, le_max_left _ _, fun L => ?_⟩
  set M := max M0 n1
  set c : ℕ → ℝ := fun n => (cnt (A p q M) n : ℝ) with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => Nat.cast_nonneg _
  have h1 := tail_le c hc0 L M y hy0 hy1.le
  rw [hy2] at h1
  have h2 : ∑ n ∈ range L, c n * y ^ n ≤ ∑ n ∈ range (L + (A p q M).sum id + 1), c n * y ^ n :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
      (fun n _ _ => mul_nonneg (hc0 n) (pow_nonneg hy0 n))
  have h3 : ∑ n ∈ range (L + (A p q M).sum id + 1), c n * y ^ n = ∏ s ∈ A p q M, (1 + y ^ s) :=
    (prod_eq_sum (A p q M) y _ (by omega)).symm
  have h4 := prod_le_exp (A p q M) y hy0 hy1
  have h5 : y ^ M ≤ y ^ n1 := pow_le_pow_of_le_one hy0 hy1.le (le_max_right _ _)
  have h6 : y ^ n1 * E < 1 / 4 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * E)] at hn1
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  have h7 : 0 ≤ ∑ n ∈ range L, c n * y ^ n :=
    sum_nonneg (fun n _ => mul_nonneg (hc0 n) (pow_nonneg hy0 n))
  have h8 : y ^ M * ∑ n ∈ range L, c n * y ^ n ≤ y ^ n1 * E := by
    apply mul_le_mul h5 (by linarith) h7 (pow_nonneg hy0 _)
  simp only [hc] at h1 h8
  linarith

/-- the core inequality under eventual monotonicity -/
theorem core_decreasing {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hcop : Nat.Coprime p q)
    {N0 : ℕ} (hcon : ∀ n, n ≥ N0 → f p q n ≤ f p q (n + 1))
    {c3 : ℝ} {N : ℕ} {ω : ℂ} (hωq : ω ^ q = 1) (hωim : c3 ≤ |ω.im|)
    (hωprod : 1 ≤ ∏ a ∈ range (N + 1), ‖1 + ω ^ (p ^ a)‖)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hxN : x ^ (p ^ N) ≤ 1 / 2)
    {M : ℕ} (hNM : p ^ N ≤ M) (hN0M : N0 ≤ M)
    (hT : ∀ L : ℕ,
      ∑ n ∈ range L, (if M ≤ n then (cnt (A p q M) n : ℝ) * x ^ n else 0) ≤ 1 / 4) :
    c3 * x * (1 / 2 ^ (N + 2) * ∏ s ∈ A p q M, (1 + x ^ s)) ≤
      (1 - x) * ∏ s ∈ A p q M, (1 + x ^ s)
        + 2 * ∑ n ∈ range (N0 + 1), (if n = 0 then 0 else (f p q (n - 1) : ℝ)) + 2 * (1 / 4) := by
  have hωn : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_one hωq (by omega)
  obtain ⟨L, hL⟩ : ∃ L, L = (A p q M).sum id + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n => (cnt (A p q M) n : ℝ) := ⟨_, rfl⟩
  have hc0 : ∀ n, 0 ≤ c n := fun n => by rw [hc]; exact Nat.cast_nonneg _
  have hcL : c L = 0 := by
    rw [hc]; simp only [cnt_eq_zero (A p q M) (show (A p q M).sum id < L by omega), Nat.cast_zero]
  have hGsum : ∏ s ∈ A p q M, (1 + x ^ s) = ∑ n ∈ range (L + 1), c n * x ^ n := by
    rw [prod_eq_sum (A p q M) x (L + 1) (by omega), hc]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ω * (x : ℂ) := ⟨_, rfl⟩
  have hznorm : ‖z‖ = x := by
    rw [hz, norm_mul, hωn, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hzsum : ∏ s ∈ A p q M, (1 + z ^ s) = ∑ n ∈ range (L + 1), (c n : ℂ) * z ^ n := by
    rw [prod_eq_sum (A p q M) z (L + 1) (by omega), hc]
    apply sum_congr rfl
    intro n _
    simp
  have hmono : ∀ n, N0 ≤ n → n < M → c n ≤ c (n + 1) := by
    intro n hn hnM
    rw [hc]
    simp only
    rw [cnt_A_eq (show n ≤ M by omega), cnt_A_eq (show n + 1 ≤ M by omega)]
    exact_mod_cast hcon n hn
  have hP := pringsheim c hc0 L hcL x hx0 hx1.le z hznorm N0 M hmono
  have hKeq : ∑ n ∈ range (N0 + 1), (if n = 0 then 0 else c (n - 1)) =
      ∑ n ∈ range (N0 + 1), (if n = 0 then 0 else (f p q (n - 1) : ℝ)) := by
    apply sum_congr rfl
    intro n hn
    split_ifs with h
    · rfl
    · rw [hc, mem_range] at *
      simp only
      rw [cnt_A_eq (show n - 1 ≤ M by omega)]
  have hTL : ∑ n ∈ range L, (if M ≤ n then c n * x ^ n else 0) ≤ 1 / 4 := by
    rw [hc]; exact hT L
  rw [hKeq, ← hzsum, ← hGsum] at hP
  have him : c3 * x ≤ ‖1 - z‖ := by
    have h1 := Complex.abs_im_le_norm (1 - z)
    have h2 : (1 - z).im = -(ω.im * x) := by simp [hz]
    rw [h2, abs_neg, abs_mul, abs_of_nonneg hx0] at h1
    nlinarith
  have htw := twisted_ge hp (by omega) hcop hNM hωq hωprod hx0 hx1.le hxN
  rw [← hz] at htw
  have e1 : ‖(1 - z) * ∏ s ∈ A p q M, (1 + z ^ s)‖ = ‖1 - z‖ * ‖∏ s ∈ A p q M, (1 + z ^ s)‖ :=
    norm_mul _ _
  have h1 : c3 * x * (1 / 2 ^ (N + 2) * ∏ s ∈ A p q M, (1 + x ^ s)) ≤
      ‖1 - z‖ * ‖∏ s ∈ A p q M, (1 + z ^ s)‖ :=
    mul_le_mul him htw (by positivity) (norm_nonneg _)
  linarith

/-- the final arithmetic of the first half -/
theorem arith_decreasing (c3 x G K0 m Q a b : ℝ) (hc3 : 0 < c3) (hx : 1 / 2 ≤ x) (hG : 0 < G)
    (hm : 0 < m) (hQ : 0 < Q)
    (hchain : c3 * x * (1 / Q * G) ≤ 1 / m * G + 2 * K0 + 2 * (1 / 4))
    (hQm : 2 * Q ≤ a * m) (hQK : 2 * Q * (2 * K0 + 1) ≤ b * G)
    (ha : a < c3 / 2) (hb : b < c3 / 2) : False := by
  have e1 : c3 * x * (1 / Q * G) = c3 * x * G / Q := by field_simp
  rw [e1, div_le_iff₀ hQ] at hchain
  have e2 : 1 / m * G * Q = (Q / m) * G := by field_simp
  have hQm' : Q / m ≤ a / 2 := by
    rw [div_le_iff₀ hm]; linarith
  have h3 : (Q / m) * G ≤ (a / 2) * G := mul_le_mul_of_nonneg_right hQm' hG.le
  have h4 : c3 * G * (1 / 2) ≤ c3 * G * x := mul_le_mul_of_nonneg_left hx (mul_pos hc3 hG).le
  have h5 : (a + b) * G < c3 * G := mul_lt_mul_of_pos_right (by linarith) hG
  have h6 : (1 / m * G + 2 * K0 + 2 * (1 / 4)) * Q = Q / m * G + Q * (2 * K0) + Q / 2 := by
    field_simp; ring
  rw [h6] at hchain
  linarith

/-- `f` is not eventually nondecreasing: the first half of the conjecture -/
theorem decreasing_io {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ N0, ∃ n ≥ N0, f p q (n + 1) < f p q n := by
  intro N0
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨c3, hc3, hroots⟩ := exists_roots (p := p) hq hcop
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ,
      K0 = ∑ n ∈ range (N0 + 1), (if n = 0 then 0 else (f p q (n - 1) : ℝ)) := ⟨_, rfl⟩
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]; exact sum_nonneg (fun n _ => by split_ifs <;> positivity)
  -- choice of `k`
  obtain ⟨k1, hk1⟩ := small_eventually (16 * (2 * K0 + 1)) ((4 : ℝ) ^ q) (c3 / 2)
    (by positivity) (by positivity) (by positivity)
  obtain ⟨k2, hk2⟩ := exists_pow_lt_of_lt_one (show 0 < c3 / 16 by positivity)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  obtain ⟨k, hk⟩ : ∃ k, k = max k1 k2 := ⟨_, rfl⟩
  have hA1 := hk1 k (by omega)
  have hA2 : (2 / 3 : ℝ) ^ k < c3 / 16 :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk2
  -- the radius
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * q * k + 1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = p ^ N := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by
    have : p ≤ p ^ N := Nat.le_self_pow (by omega) p
    omega
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 - 1 / (m : ℝ) := ⟨_, rfl⟩
  obtain ⟨hxhalf, hx1⟩ := x_bounds m hm2
  rw [← hx] at hxhalf hx1
  have hx0 : 0 ≤ x := by linarith
  have hxN : x ^ (p ^ N) ≤ 1 / 2 := by rw [hx, ← hm]; exact pow_m_le_half m (by omega)
  have hxs : ∀ s : ℕ, s ≤ p ^ (2 * q * k) → 1 / 2 ≤ x ^ s := by
    intro s hs
    rw [hx]
    apply x_pow_ge_half m s (by omega)
    have : p ^ N = p ^ (2 * q * k) * p := by rw [hN, pow_succ]
    rw [hm, this]
    nlinarith
  obtain ⟨ω, hωq, hωim, hωprod⟩ := hroots N
  obtain ⟨M, hM0, hT⟩ := exists_M p q x hx0 hx1 (max N0 m)
  have hN0M : N0 ≤ M := (le_max_left _ _).trans hM0
  have hmM : m ≤ M := (le_max_right _ _).trans hM0
  have hcore := core_decreasing hp hq hcop hcon hωq hωim hωprod hx0 hx1 hxN
    (by rw [← hm]; exact hmM) hN0M hT
  rw [← hK0] at hcore
  have hGgrowth : (3 / 2 : ℝ) ^ (k * k) ≤ ∏ s ∈ A p q M, (1 + x ^ s) :=
    prod_ge_growth (by omega) (by omega) hcop k M
      ((Nat.pow_le_pow_right (n := p) (by omega) (show 2 * q * k ≤ N by omega)).trans
        (by rw [← hm]; exact hmM)) hx0 hxs
  have hGpos : 0 < ∏ s ∈ A p q M, (1 + x ^ s) := lt_of_lt_of_le (by positivity) hGgrowth
  have h1x : 1 - x = 1 / (m : ℝ) := by rw [hx]; ring
  rw [h1x] at hcore
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQm : 2 * (2 : ℝ) ^ (N + 2) ≤ 8 * (2 / 3 : ℝ) ^ k * m := by
    have e1 : 2 * (2 : ℝ) ^ (N + 2) = 8 * (2 : ℝ) ^ N := by rw [pow_add]; ring
    have e2 : (m : ℝ) = (p : ℝ) ^ N := by rw [hm]; push_cast; ring
    rw [e1, e2]
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have h1 : (2 : ℝ) ^ N = (2 / p) ^ N * (p : ℝ) ^ N := by
      rw [← mul_pow]; congr 1; field_simp
    have h2 : (2 / (p : ℝ)) ^ N ≤ (2 / 3) ^ N :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3) N
    have h3 : (2 / 3 : ℝ) ^ N ≤ (2 / 3) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by rw [hN]; nlinarith)
    rw [h1]
    have : 0 ≤ (p : ℝ) ^ N := by positivity
    nlinarith
  have hQK : 2 * (2 : ℝ) ^ (N + 2) * (2 * K0 + 1) ≤
      16 * (2 * K0 + 1) * ((4 : ℝ) ^ q) ^ k * (2 / 3) ^ (k * k) * ∏ s ∈ A p q M, (1 + x ^ s) := by
    have e1 : 2 * (2 : ℝ) ^ (N + 2) = 16 * ((4 : ℝ) ^ q) ^ k := by
      rw [hN, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
      ring
    have e2 : (1 : ℝ) ≤ (2 / 3) ^ (k * k) * ∏ s ∈ A p q M, (1 + x ^ s) := by
      have : (2 / 3 : ℝ) ^ (k * k) * (3 / 2) ^ (k * k) = 1 := by
        rw [← mul_pow]; norm_num
      have h0 : (0 : ℝ) ≤ (2 / 3) ^ (k * k) := by positivity
      nlinarith
    rw [e1]
    have h0 : (0 : ℝ) ≤ 16 * ((4 : ℝ) ^ q) ^ k * (2 * K0 + 1) := by positivity
    nlinarith
  exact arith_decreasing c3 x _ K0 m _ _ _ hc3 hxhalf hGpos hmpos (by positivity) hcore hQm hQK
    (by linarith) hA1

/-- `f` is not eventually nonincreasing: the second half of the conjecture -/
theorem increasing_io {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ N0, ∃ n ≥ N0, f p q n < f p q (n + 1) := by
  intro N0
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ n ∈ range (N0 + 1), (f p q n : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hdesc : ∀ j, f p q (N0 + j) ≤ f p q N0 := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (hcon (N0 + j) (by omega)).trans ih
  have hfB : ∀ n, (f p q n : ℝ) ≤ B := by
    intro n
    have hle : ∀ j ∈ range (N0 + 1), (f p q j : ℝ) ≤ B := fun j hj => by
      rw [hBdef]
      exact single_le_sum (f := fun n => (f p q n : ℝ)) (fun _ _ => by positivity) hj
    rcases le_or_gt n N0 with h | h
    · exact hle n (by rw [mem_range]; omega)
    · have h1 : f p q n ≤ f p q N0 := by
        have := hdesc (n - N0); rwa [show N0 + (n - N0) = n by omega] at this
      have h2 : (f p q n : ℝ) ≤ f p q N0 := by exact_mod_cast h1
      exact h2.trans (hle N0 (by rw [mem_range]; omega))
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  obtain ⟨k, hk⟩ := small_eventually (B * p + 1) ((p : ℝ) ^ (2 * q)) 1
    (by positivity) (by positivity) one_pos
  have hA := hk k le_rfl
  obtain ⟨N, hN⟩ : ∃ N, N = 2 * q * k + 1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = p ^ N := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by
    have : p ≤ p ^ N := Nat.le_self_pow (by omega) p
    omega
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 - 1 / (m : ℝ) := ⟨_, rfl⟩
  obtain ⟨hxhalf, hx1⟩ := x_bounds m hm2
  rw [← hx] at hxhalf hx1
  have hx0 : 0 ≤ x := by linarith
  have hxs : ∀ s : ℕ, s ≤ p ^ (2 * q * k) → 1 / 2 ≤ x ^ s := by
    intro s hs
    rw [hx]
    apply x_pow_ge_half m s (by omega)
    have : p ^ N = p ^ (2 * q * k) * p := by rw [hN, pow_succ]
    rw [hm, this]
    nlinarith
  obtain ⟨M, hM0, hT⟩ := exists_M p q x hx0 hx1 m
  have hGgrowth : (3 / 2 : ℝ) ^ (k * k) ≤ ∏ s ∈ A p q M, (1 + x ^ s) :=
    prod_ge_growth (by omega) (by omega) hcop k M
      ((Nat.pow_le_pow_right (n := p) (by omega) (show 2 * q * k ≤ N by omega)).trans
        (by rw [← hm]; exact hM0)) hx0 hxs
  have hGsum : ∏ s ∈ A p q M, (1 + x ^ s) =
      ∑ n ∈ range ((A p q M).sum id + 1), (cnt (A p q M) n : ℝ) * x ^ n :=
    prod_eq_sum (A p q M) x _ (by omega)
  have hbdd := sum_le_of_bdd (fun n => (cnt (A p q M) n : ℝ)) ((A p q M).sum id + 1) x hx0 hx1 M B
    hB0 (fun n hn => by
      rw [cnt_A_eq (show n ≤ M by omega)]
      exact hfB n)
  have hTL := hT ((A p q M).sum id + 1)
  have h1x : B / (1 - x) = B * m := by
    rw [hx]
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    field_simp
    ring
  rw [← hGsum, h1x] at hbdd
  -- `B m + 1 ≤ (B p + 1) (p^{2q})^k`
  have hmreal : (m : ℝ) = ((p : ℝ) ^ (2 * q)) ^ k * p := by
    rw [hm, hN]; push_cast; rw [← pow_mul, pow_succ]
  have hone : (1 : ℝ) ≤ ((p : ℝ) ^ (2 * q)) ^ k := one_le_pow₀ (one_le_pow₀ hp1)
  have hup : B * m + 1 / 4 ≤ (B * p + 1) * ((p : ℝ) ^ (2 * q)) ^ k := by
    rw [hmreal]; nlinarith
  have h23 : (2 / 3 : ℝ) ^ (k * k) * (3 / 2) ^ (k * k) = 1 := by
    rw [← mul_pow]; norm_num
  have h0 : (0 : ℝ) ≤ (2 / 3) ^ (k * k) := by positivity
  have hG : (3 / 2 : ℝ) ^ (k * k) ≤ (B * p + 1) * ((p : ℝ) ^ (2 * q)) ^ k := by linarith
  have := mul_le_mul_of_nonneg_left hG h0
  nlinarith

/-- **MathDB 367529** (Ding–Liu–Wang, Conjecture 3). -/
theorem ding_liu_wang_conj3 (p q : ℕ) (hp : 2 < p) (hpq : p < q) (hcop : Nat.Coprime p q) :
    (∀ N, ∃ n ≥ N, f p q (n + 1) < f p q n) ∧ (∀ N, ∃ n ≥ N, f p q n < f p q (n + 1)) :=
  ⟨decreasing_io (by omega) (by omega) hcop, increasing_io (by omega) (by omega) hcop⟩

theorem conj3 : Conj3 := fun p q hp hpq hcop => ding_liu_wang_conj3 p q hp hpq hcop

end Fpq

#check @Fpq.ding_liu_wang_conj3
#print Fpq.BE
#print Fpq.f
#print Fpq.Conj3
#print axioms Fpq.ding_liu_wang_conj3
#print axioms Fpq.conj3
#print axioms Fpq.f_3_4_1
#print axioms Fpq.f_3_4_2
#print axioms Fpq.f_3_4_0
#print axioms Fpq.zero_not_mem_BE
```

