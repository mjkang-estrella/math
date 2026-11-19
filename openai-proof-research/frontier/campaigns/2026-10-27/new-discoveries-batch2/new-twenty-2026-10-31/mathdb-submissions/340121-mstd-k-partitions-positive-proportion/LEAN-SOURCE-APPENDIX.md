# Lean source appendix

Modules are listed in import order.

## MstdCount.lean

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith

/-!
# Counting lemmas for colourings with independent coordinates

`Free S x`: the finite set `S` of maps `I → β` is closed under changing the value at `x`.
For such sets, conditioning on the value at `x` splits `S` into fibres of equal size.  This
gives exact counts for events on disjoint coordinates; they replace the probabilistic
independence arguments of the paper.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset

variable {I β : Type*} [DecidableEq I] [Fintype I] [Fintype β] [DecidableEq β]

/-- `S` is free at the coordinate `x`. -/
def Free (S : Finset (I → β)) (x : I) : Prop :=
  ∀ ω ∈ S, ∀ a, Function.update ω x a ∈ S

theorem free_univ (x : I) : Free (univ : Finset (I → β)) x := fun _ _ _ => mem_univ _

theorem card_fiber_eq {S : Finset (I → β)} {x : I} (hS : Free S x) (a b : β) :
    #(S.filter fun ω => ω x = a) = #(S.filter fun ω => ω x = b) := by
  refine Finset.card_bij' (fun ω _ => Function.update ω x b)
    (fun ω _ => Function.update ω x a) ?_ ?_ ?_ ?_
  · intro ω hω
    rw [mem_filter] at hω ⊢
    exact ⟨hS ω hω.1 b, by simp⟩
  · intro ω hω
    rw [mem_filter] at hω ⊢
    exact ⟨hS ω hω.1 a, by simp⟩
  · intro ω hω
    rw [mem_filter] at hω
    rw [Function.update_idem, ← hω.2, Function.update_eq_self]
  · intro ω hω
    rw [mem_filter] at hω
    rw [Function.update_idem, ← hω.2, Function.update_eq_self]

/-- **Single-coordinate lemma.** -/
theorem card_filter_mem_mul {S : Finset (I → β)} {x : I} (hS : Free S x) (G : Finset β) :
    #(S.filter fun ω => ω x ∈ G) * Fintype.card β = #S * #G := by
  set F : β → ℕ := fun a => #(S.filter fun ω => ω x = a) with hF
  have h1 : #(S.filter fun ω => ω x ∈ G) = ∑ a ∈ G, F a := by
    rw [card_eq_sum_card_fiberwise (s := S.filter fun ω => ω x ∈ G)
      (f := fun ω : I → β => ω x) (t := G) (fun ω hω => (mem_filter.1 (mem_coe.1 hω)).2)]
    refine sum_congr rfl fun a ha => ?_
    rw [filter_filter]
    congr 1
    refine filter_congr fun ω _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ ha, h⟩
  have h2 : #S = ∑ a, F a :=
    card_eq_sum_card_fiberwise (f := fun ω : I → β => ω x) (t := univ) (fun _ _ => by simp)
  have h3 : ∀ a, F a * Fintype.card β = ∑ b, F b := by
    intro a
    rw [← Finset.card_univ, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact sum_congr rfl fun b _ => card_fiber_eq hS a b
  rw [h1, h2, Finset.sum_mul, Finset.sum_congr rfl fun a _ => h3 a, sum_const, smul_eq_mul,
    mul_comm]

theorem free_filter_of_ne {S : Finset (I → β)} {x y : I} (hxy : x ≠ y) (hy : Free S y)
    (P : β → Prop) [DecidablePred P] : Free (S.filter fun ω => P (ω x)) y := by
  intro ω hω a
  rw [mem_filter] at hω ⊢
  refine ⟨hy ω hω.1 a, ?_⟩
  rw [Function.update_of_ne hxy]
  exact hω.2

/-- **Pair lemma.** -/
theorem card_filter_pair {S : Finset (I → β)} {x y : I} (hxy : x ≠ y) (hx : Free S x)
    (hy : Free S y) (G G' : Finset β) :
    #(S.filter fun ω => ¬(ω x ∈ G ∧ ω y ∈ G')) * Fintype.card β ^ 2 + #S * (#G * #G') =
      #S * Fintype.card β ^ 2 := by
  set S1 := S.filter fun ω => ω x ∈ G
  have hS1 := card_filter_mem_mul hx G
  have hS1y : Free S1 y := free_filter_of_ne hxy hy (fun b => b ∈ G)
  have hS2 := card_filter_mem_mul hS1y G'
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun ω => ω x ∈ G ∧ ω y ∈ G')
  have hS2' : #(S.filter fun ω => ω x ∈ G ∧ ω y ∈ G') = #(S1.filter fun ω => ω y ∈ G') := by
    rw [filter_filter]
  set B := Fintype.card β
  set n := #(S.filter fun ω => ¬(ω x ∈ G ∧ ω y ∈ G'))
  set m := #(S.filter fun ω => ω x ∈ G ∧ ω y ∈ G')
  have hm : m * B ^ 2 = #S * (#G * #G') := by
    rw [hS2']
    calc #(S1.filter fun ω => ω y ∈ G') * B ^ 2
        = (#(S1.filter fun ω => ω y ∈ G') * B) * B := by ring
      _ = (#S1 * #G') * B := by rw [hS2]
      _ = (#S1 * B) * #G' := by ring
      _ = (#S * #G) * #G' := by rw [hS1]
      _ = #S * (#G * #G') := by ring
  calc n * B ^ 2 + #S * (#G * #G') = n * B ^ 2 + m * B ^ 2 := by rw [hm]
    _ = (m + n) * B ^ 2 := by ring
    _ = #S * B ^ 2 := by rw [hsplit]

/-- **Iterated pair lemma.**  For `n` pairwise disjoint pairs of free coordinates and events
"`ω (X j) ∈ G j` and `ω (Y j) ∈ G' j`" with `|G j| = |G' j| = c` and `|β| = k c`,
the number of `ω ∈ S` avoiding all events is `#S ((k^2-1)/k^2)^n`. -/
theorem card_iter_pair (k c : ℕ) (hβ : Fintype.card β = k * c) (hc : 0 < c) (hk : 1 ≤ k)
    (S : Finset (I → β)) (n : ℕ) (X Y : ℕ → I) (G G' : ℕ → Finset β)
    (hG : ∀ j, #(G j) = c) (hG' : ∀ j, #(G' j) = c)
    (hXY : ∀ j < n, ∀ j' < n, X j ≠ Y j')
    (hXX : ∀ j < n, ∀ j' < n, j ≠ j' → X j ≠ X j')
    (hYY : ∀ j < n, ∀ j' < n, j ≠ j' → Y j ≠ Y j')
    (hfX : ∀ j < n, Free S (X j)) (hfY : ∀ j < n, Free S (Y j)) :
    #(S.filter fun ω => ∀ j < n, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j)) * k ^ (2 * n) =
      #S * (k ^ 2 - 1) ^ n := by
  have key : ∀ m ≤ n, #(S.filter fun ω => ∀ j < m, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j)) *
      k ^ (2 * m) = #S * (k ^ 2 - 1) ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      set Tm := S.filter fun ω => ∀ j < m, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j)
      have hfree : ∀ z, (∀ j < m, X j ≠ z ∧ Y j ≠ z) → Free S z → Free Tm z := by
        intro z hz hSz ω hω a
        rw [mem_filter] at hω ⊢
        refine ⟨hSz ω hω.1 a, fun j hj => ?_⟩
        rw [Function.update_of_ne (hz j hj).1, Function.update_of_ne (hz j hj).2]
        exact hω.2 j hj
      have hTX : Free Tm (X m) := hfree _ (fun j hj => ⟨hXX j (by omega) m (by omega) (by omega),
        fun h => hXY m (by omega) j (by omega) h.symm⟩) (hfX m (by omega))
      have hTY : Free Tm (Y m) := hfree _ (fun j hj => ⟨hXY j (by omega) m (by omega),
        hYY j (by omega) m (by omega) (by omega)⟩) (hfY m (by omega))
      have hstep := card_filter_pair (hXY m (by omega) m (by omega)) hTX hTY (G m) (G' m)
      have hset : (S.filter fun ω => ∀ j < m + 1, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j)) =
          Tm.filter fun ω => ¬(ω (X m) ∈ G m ∧ ω (Y m) ∈ G' m) := by
        rw [filter_filter]
        refine filter_congr fun ω _ => ?_
        constructor
        · intro h
          exact ⟨fun j hj => h j (by omega), h m (by omega)⟩
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact h1 j hj
          · exact h2
      rw [hset]
      rw [hG, hG', hβ] at hstep
      set u := #(Tm.filter fun ω => ¬(ω (X m) ∈ G m ∧ ω (Y m) ∈ G' m))
      have hc2 : 0 < c * c := Nat.mul_pos hc hc
      have h1 : (u * k ^ 2 + #Tm) * (c * c) = (#Tm * k ^ 2) * (c * c) := by
        calc (u * k ^ 2 + #Tm) * (c * c) = u * (k * c) ^ 2 + #Tm * (c * c) := by ring
          _ = #Tm * (k * c) ^ 2 := hstep
          _ = (#Tm * k ^ 2) * (c * c) := by ring
      have h2 : u * k ^ 2 + #Tm = #Tm * k ^ 2 := Nat.eq_of_mul_eq_mul_right hc2 h1
      have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
      have h3 : u * k ^ 2 = #Tm * (k ^ 2 - 1) := by
        rw [Nat.mul_sub, mul_one]
        omega
      have ih' := ih (by omega)
      calc u * k ^ (2 * (m + 1)) = (u * k ^ 2) * k ^ (2 * m) := by ring
        _ = #Tm * (k ^ 2 - 1) * k ^ (2 * m) := by rw [h3]
        _ = (#Tm * k ^ (2 * m)) * (k ^ 2 - 1) := by ring
        _ = #S * (k ^ 2 - 1) ^ m * (k ^ 2 - 1) := by rw [ih']
        _ = #S * (k ^ 2 - 1) ^ (m + 1) := by ring
  exact key n le_rfl

/-- **Iterated single-coordinate lemma.** -/
theorem card_iter_single (q g : ℕ) (hβ : Fintype.card β = q)
    (S : Finset (I → β)) (n : ℕ) (X : ℕ → I) (G : ℕ → Finset β) (hG : ∀ j, #(G j) = g)
    (hXX : ∀ j < n, ∀ j' < n, j ≠ j' → X j ≠ X j')
    (hfX : ∀ j < n, Free S (X j)) :
    #(S.filter fun ω => ∀ j < n, ω (X j) ∈ G j) * q ^ n = #S * g ^ n := by
  have key : ∀ m ≤ n, #(S.filter fun ω => ∀ j < m, ω (X j) ∈ G j) * q ^ m = #S * g ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      set Tm := S.filter fun ω => ∀ j < m, ω (X j) ∈ G j
      have hTX : Free Tm (X m) := by
        intro ω hω a
        rw [mem_filter] at hω ⊢
        refine ⟨hfX m (by omega) ω hω.1 a, fun j hj => ?_⟩
        rw [Function.update_of_ne (hXX j (by omega) m (by omega) (by omega))]
        exact hω.2 j hj
      have hstep := card_filter_mem_mul hTX (G m)
      have hset : (S.filter fun ω => ∀ j < m + 1, ω (X j) ∈ G j) =
          Tm.filter fun ω => ω (X m) ∈ G m := by
        rw [filter_filter]
        refine filter_congr fun ω _ => ?_
        constructor
        · intro h
          exact ⟨fun j hj => h j (by omega), h m (by omega)⟩
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact h1 j hj
          · exact h2
      rw [hset]
      rw [hG, hβ] at hstep
      have ih' := ih (by omega)
      calc #(Tm.filter fun ω => ω (X m) ∈ G m) * q ^ (m + 1)
          = (#(Tm.filter fun ω => ω (X m) ∈ G m) * q) * q ^ m := by ring
        _ = (#Tm * g) * q ^ m := by rw [hstep]
        _ = (#Tm * q ^ m) * g := by ring
        _ = #S * g ^ m * g := by rw [ih']
        _ = #S * g ^ (m + 1) := by ring
  exact key n le_rfl

end Mstd340121
```

## MstdDefs.lean

```lean
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

/-!
# Definitions for MathDB 340121

Chu, Luntzlara, Miller and Shao (arXiv:1808.05460, INTEGERS 19 (2019)), Conjecture 1.5:
"For any finite `k ≥ 2`, the proportion of `k`-decompositions into MSTD subsets is bounded
below by a positive constant."  A `k`-decomposition of `I_r = {1, …, r}` is a partition into
`k` (nonempty, pairwise disjoint) sets; `A` is MSTD if `|A + A| > |A - A|`.
-/

namespace Mstd340121

open Finset Pointwise

/-- `A` is MSTD (more sums than differences): `|A - A| < |A + A|`. -/
def MSTD (A : Finset ℤ) : Prop := (A - A).card < (A + A).card

instance : DecidablePred MSTD := fun _ => inferInstanceAs (Decidable (_ < _))

/-- The colour class of colour `i`, placed on `{1, …, r}`. -/
def cls {r k : ℕ} (c : Fin r → Fin k) (i : Fin k) : Finset ℤ :=
  (univ.filter fun j => c j = i).image fun j : Fin r => (j : ℤ) + 1

/-- Labelled `k`-colourings of `{1, …, r}` all of whose colour classes are MSTD. -/
def goodColourings (r k : ℕ) : Finset (Fin r → Fin k) :=
  univ.filter fun c => ∀ i, MSTD (cls c i)

/-- The block `s ⊆ Fin r` placed on `{1, …, r}`. -/
def place {r : ℕ} (s : Finset (Fin r)) : Finset ℤ := s.image fun j : Fin r => (j : ℤ) + 1

/-- All partitions of `{1, …, r}` (indexed by `Fin r`) into exactly `k` blocks. -/
def allPartitions (r k : ℕ) : Finset (Finpartition (univ : Finset (Fin r))) :=
  univ.filter fun P => P.parts.card = k

/-- Partitions of `{1, …, r}` into exactly `k` blocks, every block MSTD. -/
def goodPartitions (r k : ℕ) : Finset (Finpartition (univ : Finset (Fin r))) :=
  univ.filter fun P => P.parts.card = k ∧ ∀ s ∈ P.parts, MSTD (place s)

/-- **Conjecture 1.5 (proportion form).**  For every `k ≥ 2` there are `c > 0` and `R` such
that for all `r ≥ R` the proportion of `k`-decompositions of `{1, …, r}` into MSTD subsets
among all `k`-decompositions is at least `c`. -/
def Conjecture15 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℚ, 0 < c ∧ ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
    c ≤ ((goodPartitions r k).card : ℚ) / (allPartitions r k).card

/-- **Conjecture 1.5 (counting form, unordered partitions).** -/
def Conjecture15Count : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ D R : ℕ, 0 < D ∧ ∀ r : ℕ, R ≤ r →
    (allPartitions r k).card ≤ D * (goodPartitions r k).card

/-- **Labelled form**: among all `k ^ r` colourings `Fin r → Fin k`, a positive proportion has
every colour class MSTD. -/
def LabelledPositiveProportion : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ D R : ℕ, 0 < D ∧ ∀ r : ℕ, R ≤ r →
    k ^ r ≤ D * (goodColourings r k).card

/-- MSTD is invariant under translation. -/
theorem mstd_image_add_iff (A : Finset ℤ) (t : ℤ) :
    MSTD (A.image fun x => x + t) ↔ MSTD A := by
  unfold MSTD
  have hd : (A.image fun x => x + t) - (A.image fun x => x + t) = A - A := by
    ext z
    simp only [mem_sub, mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha, b, hb, by ring⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a + t, ⟨a, ha, rfl⟩, b + t, ⟨b, hb, rfl⟩, by ring⟩
  have hs : (A.image fun x => x + t) + (A.image fun x => x + t) =
      (A + A).image fun x => x + 2 * t := by
    ext z
    simp only [mem_add, mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by ring⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a + t, ⟨a, ha, rfl⟩, b + t, ⟨b, hb, rfl⟩, by ring⟩
  rw [hd, hs, card_image_of_injective _ (add_left_injective _)]

end Mstd340121
```

## MstdModular.lean

```lean
import MstdCount
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp

/-!
# The modular colouring

For every `k ≥ 2` there are an odd `h` and a colouring `F : ℤ → Fin k`, periodic with
period `2h`, such that

1. `F (x + h) ≠ F x` for every `x` (antipodal points get different colours), and
2. for every colour `i` and every `s` there is `u` with `F u = i` and `F (s - u) = i`.

Proof: the random colouring giving each antipodal pair `{t, t + h}` (`t` mod `h`) a uniform
ordered pair of distinct colours; the even point gets the first colour.  For fixed `s` and
`i`, `m = (h - 1) / 2` disjoint pairs of coordinates each represent `s`, so the number of
colourings in which `s ∉ B_i + B_i` is at most a fraction `(1 - 1/k^2)^m`, and a union bound
over the `2hk` events finishes.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset

/-- Ordered pairs of distinct colours. -/
abbrev Pi2 (k : ℕ) := {q : Fin k × Fin k // q.1 ≠ q.2}

/-- Select the colour of an antipodal pair for parity `e`. -/
def sel {k : ℕ} (e : ℤ) (π : Pi2 k) : Fin k := if e = 0 then π.1.1 else π.1.2

/-- The colouring of `ℤ` determined by `ω : ZMod h → Pi2 k`. -/
def colOf {k h : ℕ} (ω : ZMod h → Pi2 k) (x : ℤ) : Fin k := sel (x % 2) (ω x)

theorem card_pi2 (k : ℕ) : Fintype.card (Pi2 k) = k * (k - 1) := by
  rw [Fintype.card_subtype]
  have : (univ.filter fun q : Fin k × Fin k => q.1 ≠ q.2) = (univ : Finset (Fin k)).offDiag := by
    ext q
    simp [mem_offDiag]
  rw [this, offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub, mul_one]

theorem card_sel_filter (k : ℕ) (e : ℤ) (i : Fin k) :
    #(univ.filter fun π : Pi2 k => sel e π = i) = k - 1 := by
  have key : ∀ (g : Fin k × Fin k → Fin k) (o : Fin k × Fin k → Fin k),
      (∀ q, g q = q.1 ∧ o q = q.2 ∨ g q = q.2 ∧ o q = q.1) →
      (∀ c, #(univ.filter fun q : Fin k × Fin k => q.1 ≠ q.2 ∧ g q = c) = k - 1) →
      #(univ.filter fun π : Pi2 k => g π.1 = i) = k - 1 := by
    intro g o _ hc
    rw [← hc i]
    refine card_bij (fun π _ => π.1) ?_ ?_ ?_
    · intro π hπ
      rw [mem_filter] at hπ ⊢
      exact ⟨mem_univ _, π.2, hπ.2⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro q hq
      rw [mem_filter] at hq
      exact ⟨⟨q, hq.2.1⟩, by simp [hq.2.2], rfl⟩
  have hfst : ∀ c : Fin k,
      #(univ.filter fun q : Fin k × Fin k => q.1 ≠ q.2 ∧ q.1 = c) = k - 1 := by
    intro c
    have : (univ.filter fun q : Fin k × Fin k => q.1 ≠ q.2 ∧ q.1 = c) =
        ({c} : Finset (Fin k)) ×ˢ (univ.erase c) := by
      ext q
      simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, mem_erase,
        and_true]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, fun h => h1 (h2.trans h.symm)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h2 (h.symm.trans h1), h1⟩
    rw [this, card_product, card_singleton, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, one_mul]
  have hsnd : ∀ c : Fin k,
      #(univ.filter fun q : Fin k × Fin k => q.1 ≠ q.2 ∧ q.2 = c) = k - 1 := by
    intro c
    have : (univ.filter fun q : Fin k × Fin k => q.1 ≠ q.2 ∧ q.2 = c) =
        (univ.erase c) ×ˢ ({c} : Finset (Fin k)) := by
      ext q
      simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, mem_erase,
        and_true]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (h.trans h2.symm), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (h.trans h2), h2⟩
    rw [this, card_product, card_singleton, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, mul_one]
  unfold sel
  by_cases he : e = 0
  · simp only [he, ite_true]
    exact key (fun q => q.1) (fun q => q.2) (fun q => Or.inl ⟨rfl, rfl⟩) hfst
  · simp only [he, ite_false]
    exact key (fun q => q.2) (fun q => q.1) (fun q => Or.inr ⟨rfl, rfl⟩) hsnd

theorem colOf_congr {k h : ℕ} (ω : ZMod h → Pi2 k) {x y : ℤ}
    (hxy : x ≡ y [ZMOD (2 * h : ℕ)]) : colOf ω x = colOf ω y := by
  unfold colOf
  have h1 : (x : ZMod h) = (y : ZMod h) := by
    rw [ZMod.intCast_eq_intCast_iff]
    have : x ≡ y [ZMOD ((h : ℕ) : ℤ) * 2] := by
      have := hxy
      push_cast at this ⊢
      rwa [mul_comm] at this
    exact Int.ModEq.of_mul_right 2 this
  have h2 : x % 2 = y % 2 := by
    have : x ≡ y [ZMOD 2 * ((h : ℕ) : ℤ)] := by
      have := hxy
      push_cast at this ⊢
      exact this
    exact Int.ModEq.of_mul_right _ this
  rw [h1, h2]

theorem colOf_antipodal {k h : ℕ} (hh : Odd h) (ω : ZMod h → Pi2 k) (x : ℤ) :
    colOf ω (x + h) ≠ colOf ω x := by
  unfold colOf sel
  have h1 : (((x + h : ℤ)) : ZMod h) = (x : ZMod h) := by
    push_cast
    simp
  rw [h1]
  obtain ⟨j, hj⟩ := hh
  have hpar : (x + h) % 2 ≠ x % 2 := by
    rw [hj]
    push_cast
    omega
  have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hx2 with h0 | h0
  · have : (x + h) % 2 ≠ 0 := by rw [h0] at hpar; exact hpar
    simp only [this, h0, ite_true, ite_false]
    exact fun e => (ω x).2 e.symm
  · have : (x + h) % 2 = 0 := by
      rw [h0] at hpar
      omega
    have h0' : x % 2 ≠ 0 := by omega
    simp only [this, h0', ite_true, ite_false]
    exact (ω x).2

/-- Nonzero small residues: if `0 < z < h` then `h ∤ z`. -/
theorem no_small_dvd {h z : ℤ} (hd : h ∣ z) (hz : 0 < z) (hzh : z < h) : False := by
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt hz.le hzh hd
  omega

open Classical in
/-- The number of colourings `ω` for which `s` has no representation in colour `i`. -/
theorem bad_count {k m : ℕ} (hk : 2 ≤ k) (s : ℤ) (i : Fin k) :
    #(univ.filter fun ω : ZMod (2 * m + 1) → Pi2 k =>
        ¬ ∃ u, colOf ω u = i ∧ colOf ω (s - u) = i) * k ^ (2 * m) ≤
      Fintype.card (ZMod (2 * m + 1) → Pi2 k) * (k ^ 2 - 1) ^ m := by
  set h := 2 * m + 1 with hh
  set t0 : ℤ := s * (m + 1) with ht0
  let U : ℕ → ℤ := fun d => t0 + d + 1
  let X : ℕ → ZMod h := fun d => ((U d : ℤ) : ZMod h)
  let Y : ℕ → ZMod h := fun d => ((s - U d : ℤ) : ZMod h)
  let G : ℕ → Finset (Pi2 k) := fun d => univ.filter fun π => sel (U d % 2) π = i
  let G' : ℕ → Finset (Pi2 k) := fun d => univ.filter fun π => sel ((s - U d) % 2) π = i
  have hdiv : ((h : ℕ) : ℤ) ∣ 2 * t0 - s := ⟨s, by rw [ht0, hh]; push_cast; ring⟩
  have hcast : ∀ a b : ℤ, ((a : ZMod h) = (b : ZMod h)) → ((h : ℕ) : ℤ) ∣ b - a := by
    intro a b hab
    rw [ZMod.intCast_eq_intCast_iff] at hab
    exact Int.ModEq.dvd hab
  have hhpos : ((h : ℕ) : ℤ) = 2 * m + 1 := by rw [hh]; push_cast; ring
  have hXY : ∀ j < m, ∀ j' < m, X j ≠ Y j' := by
    intro j hj j' hj' he
    have h1 := hcast _ _ he
    have h2 : ((h : ℕ) : ℤ) ∣ -(((s - U j' : ℤ) - U j) + (2 * t0 - s)) := by
      exact (dvd_neg).2 (dvd_add h1 hdiv)
    have h3 : -(((s - U j' : ℤ) - U j) + (2 * t0 - s)) = (j : ℤ) + j' + 2 := by
      simp only [U]
      ring
    rw [h3] at h2
    exact no_small_dvd h2 (by positivity) (by rw [hhpos]; omega)
  have hXX : ∀ j < m, ∀ j' < m, j ≠ j' → X j ≠ X j' := by
    intro j hj j' hj' hne he
    have h1 := hcast _ _ he
    have h3 : (U j' : ℤ) - U j = (j' : ℤ) - j := by simp only [U]; ring
    rw [h3] at h1
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact no_small_dvd h1 (by omega) (by rw [hhpos]; omega)
    · have h1' : ((h : ℕ) : ℤ) ∣ (j : ℤ) - j' := by
        have := (dvd_neg).2 h1
        rwa [neg_sub] at this
      exact no_small_dvd h1' (by omega) (by rw [hhpos]; omega)
  have hYY : ∀ j < m, ∀ j' < m, j ≠ j' → Y j ≠ Y j' := by
    intro j hj j' hj' hne he
    have h1 := hcast _ _ he
    have h3 : (s - U j' : ℤ) - (s - U j) = (j : ℤ) - j' := by simp only [U]; ring
    rw [h3] at h1
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1' : ((h : ℕ) : ℤ) ∣ (j' : ℤ) - j := by
        have := (dvd_neg).2 h1
        rwa [neg_sub] at this
      exact no_small_dvd h1' (by omega) (by rw [hhpos]; omega)
    · exact no_small_dvd h1 (by omega) (by rw [hhpos]; omega)
  have hcount := card_iter_pair k (k - 1) (by rw [card_pi2]) (by omega) (by omega)
    (univ : Finset (ZMod h → Pi2 k)) m X Y G G'
    (fun j => card_sel_filter k _ i) (fun j => card_sel_filter k _ i)
    hXY hXX hYY (fun j _ => free_univ _) (fun j _ => free_univ _)
  have hsub : (univ.filter fun ω : ZMod h → Pi2 k =>
        ¬ ∃ u, colOf ω u = i ∧ colOf ω (s - u) = i) ⊆
      univ.filter fun ω => ∀ j < m, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j) := by
    intro ω hω
    rw [mem_filter] at hω ⊢
    refine ⟨mem_univ _, fun j _ hj => hω.2 ⟨U j, ?_, ?_⟩⟩
    · have := (mem_filter.1 hj.1).2
      exact this
    · have := (mem_filter.1 hj.2).2
      exact this
  calc #(univ.filter fun ω : ZMod h → Pi2 k =>
        ¬ ∃ u, colOf ω u = i ∧ colOf ω (s - u) = i) * k ^ (2 * m)
      ≤ #(univ.filter fun ω : ZMod h → Pi2 k =>
          ∀ j < m, ¬(ω (X j) ∈ G j ∧ ω (Y j) ∈ G' j)) * k ^ (2 * m) :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ = Fintype.card (ZMod h → Pi2 k) * (k ^ 2 - 1) ^ m := by
        rw [hcount, card_univ]

/-- A suitable `m`: `(4m + 2) k (k^2 - 1)^m < k^(2m)`. -/
theorem exists_good_m {k : ℕ} (hk : 2 ≤ k) :
    ∃ m : ℕ, 1 ≤ m ∧ (4 * m + 2) * k * (k ^ 2 - 1) ^ m < k ^ (2 * m) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set b : ℝ := ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 with hb
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hb0 : 0 ≤ b := by rw [hb]; apply div_nonneg <;> nlinarith
  have hb1 : b < 1 := by rw [hb, div_lt_one hk2]; linarith
  have ht := tendsto_self_mul_const_pow_of_lt_one hb0 hb1
  have hε : (0 : ℝ) < 1 / (6 * k) := by positivity
  obtain ⟨m, hm⟩ := ((ht.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨m, hm.2, ?_⟩
  have h1 : (m : ℝ) * b ^ m < 1 / (6 * k) := hm.1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.2
  have hbm : 0 ≤ b ^ m := pow_nonneg hb0 m
  have h2 : (4 * (m : ℝ) + 2) * k * b ^ m < 1 := by
    have h3 : (4 * (m : ℝ) + 2) * k * b ^ m ≤ 6 * k * ((m : ℝ) * b ^ m) := by
      have : (4 * (m : ℝ) + 2) ≤ 6 * m := by linarith
      have hk0 : (0 : ℝ) ≤ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hk0 hbm)]
    have h4 : 6 * k * ((m : ℝ) * b ^ m) < 6 * k * (1 / (6 * k)) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    have h5 : 6 * (k : ℝ) * (1 / (6 * k)) = 1 := by field_simp
    linarith
  have hpow : b ^ m * ((k : ℝ) ^ 2) ^ m = ((k : ℝ) ^ 2 - 1) ^ m := by
    rw [← mul_pow, hb, div_mul_cancel₀ _ hk2.ne']
  have hreal : (4 * (m : ℝ) + 2) * k * ((k : ℝ) ^ 2 - 1) ^ m < ((k : ℝ) ^ 2) ^ m := by
    rw [← hpow]
    have hpos : (0 : ℝ) < ((k : ℝ) ^ 2) ^ m := by positivity
    nlinarith
  have hk1 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hcast : (((k ^ 2 - 1 : ℕ)) : ℝ) = (k : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub hk1]
    push_cast
    ring
  rw [← pow_mul] at hreal
  have : (((4 * m + 2) * k * (k ^ 2 - 1) ^ m : ℕ) : ℝ) < ((k ^ (2 * m) : ℕ) : ℝ) := by
    push_cast [hcast]
    rw [hcast] at *
    exact hreal
  exact_mod_cast this

/-- **The modular lemma.** -/
theorem exists_modular {k : ℕ} (hk : 2 ≤ k) :
    ∃ h : ℕ, Odd h ∧ ∃ F : ℤ → Fin k,
      (∀ x y, x ≡ y [ZMOD (2 * h : ℕ)] → F x = F y) ∧ (∀ x, F (x + h) ≠ F x) ∧
      (∀ i s, ∃ u, F u = i ∧ F (s - u) = i) := by
  classical
  obtain ⟨m, _, hm⟩ := exists_good_m hk
  set h := 2 * m + 1 with hh
  have hodd : Odd h := ⟨m, rfl⟩
  -- the bad events, indexed by `s ∈ [0, 2h)` and colours `i`
  let E : Finset (ℕ × Fin k) := (range (2 * h)) ×ˢ univ
  let bad : ℕ × Fin k → Finset (ZMod h → Pi2 k) := fun si =>
    univ.filter fun ω => ¬ ∃ u, colOf ω u = si.2 ∧ colOf ω ((si.1 : ℤ) - u) = si.2
  have hcardE : #E = 2 * h * k := by simp [E, card_product]
  have hsum : (∑ si ∈ E, #(bad si)) * k ^ (2 * m) ≤
      #E * (Fintype.card (ZMod h → Pi2 k) * (k ^ 2 - 1) ^ m) := by
    rw [Finset.sum_mul]
    calc ∑ si ∈ E, #(bad si) * k ^ (2 * m)
        ≤ ∑ _si ∈ E, Fintype.card (ZMod h → Pi2 k) * (k ^ 2 - 1) ^ m :=
          Finset.sum_le_sum fun si _ => bad_count hk (si.1 : ℤ) si.2
      _ = #E * (Fintype.card (ZMod h → Pi2 k) * (k ^ 2 - 1) ^ m) := by
          rw [sum_const, smul_eq_mul]
  have hlt : ∑ si ∈ E, #(bad si) < Fintype.card (ZMod h → Pi2 k) := by
    have hpos : 0 < Fintype.card (ZMod h → Pi2 k) := by
      rw [Fintype.card_fun, card_pi2, ZMod.card]
      exact Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
    have hkpos : 0 < k ^ (2 * m) := by positivity
    by_contra hge
    rw [not_lt] at hge
    have h1 := Nat.mul_le_mul_right (k ^ (2 * m)) hge
    have h2 : Fintype.card (ZMod h → Pi2 k) * k ^ (2 * m) ≤
        Fintype.card (ZMod h → Pi2 k) * ((4 * m + 2) * k * (k ^ 2 - 1) ^ m) := by
      calc Fintype.card (ZMod h → Pi2 k) * k ^ (2 * m) ≤ (∑ si ∈ E, #(bad si)) * k ^ (2 * m) := h1
        _ ≤ #E * (Fintype.card (ZMod h → Pi2 k) * (k ^ 2 - 1) ^ m) := hsum
        _ = Fintype.card (ZMod h → Pi2 k) * ((4 * m + 2) * k * (k ^ 2 - 1) ^ m) := by
            have h2h : 2 * h = 4 * m + 2 := by omega
            rw [hcardE, h2h]; ring
    have h3 := Nat.le_of_mul_le_mul_left h2 hpos
    omega
  have hex : ∃ ω, ω ∉ E.biUnion bad := by
    by_contra hall
    push Not at hall
    have h1 : (univ : Finset (ZMod h → Pi2 k)) ⊆ E.biUnion bad := fun ω _ => hall ω
    have h2 := card_le_card h1
    have h3 := card_biUnion_le (s := E) (t := bad)
    rw [card_univ] at h2
    omega
  obtain ⟨ω, hω⟩ := hex
  refine ⟨h, hodd, colOf ω, fun x y hxy => colOf_congr ω hxy, colOf_antipodal hodd ω, ?_⟩
  intro i s
  set s' : ℤ := s % (2 * h : ℕ) with hs'
  have hs'0 : 0 ≤ s' := Int.emod_nonneg _ (by positivity)
  have hs'1 : s' < (2 * h : ℕ) := Int.emod_lt_of_pos _ (by positivity)
  have hmem : (s'.toNat, i) ∈ E := by
    simp only [E, mem_product, mem_range, mem_univ, and_true]
    omega
  have hnot : (ω ∉ bad (s'.toNat, i)) := fun hb => hω (mem_biUnion.2 ⟨_, hmem, hb⟩)
  simp only [bad, mem_filter, mem_univ, true_and, not_not] at hnot
  obtain ⟨u, hu1, hu2⟩ := hnot
  refine ⟨u, hu1, ?_⟩
  rw [← hu2]
  apply colOf_congr
  have : ((s'.toNat : ℕ) : ℤ) = s' := Int.toNat_of_nonneg hs'0
  rw [this]
  exact Int.ModEq.sub_right _ (Int.mod_modEq _ _).symm

end Mstd340121
```

## MstdInterval.lean

```lean
import MstdCount
import MstdDefs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# Colourings of the interval `[0, N]`

* `pt N n` is the position `n` (clamped to `N`), `cl ω i` the colour class of `i` as a set of
  integers in `[0, N]`.
* `Omega N T F` is the set of colourings agreeing with `F` on the two fringes `[0, T - 1]`
  and `[N - T + 1, N]`; it has `k ^ (N + 1 - 2T)` elements and is free in the middle.
* `det_low`: a fringe coloured periodically by `G` with full modular self-sums puts every
  `s ∈ [p - 1, 2T - p - 1]` into every `cl ω i + cl ω i`.
* `card_sub_cl_le`: if both fringes are coloured by an antipodally proper periodic `F`, every
  class misses `2Q` extreme differences.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset Pointwise

variable {k : ℕ}

/-- Position `n` of `[0, N]` (clamped). -/
def pt (N n : ℕ) : Fin (N + 1) := ⟨min n N, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem pt_val {N n : ℕ} (h : n ≤ N) : (pt N n).val = n := by
  simp [pt, h]

theorem pt_ne {N n n' : ℕ} (h : n ≤ N) (h' : n' ≤ N) (hne : n ≠ n') : pt N n ≠ pt N n' :=
  fun e => hne (by have := congrArg Fin.val e; rwa [pt_val h, pt_val h'] at this)

theorem pt_fin {N : ℕ} (j : Fin (N + 1)) : pt N j.val = j :=
  Fin.ext (pt_val (Nat.lt_succ_iff.1 j.isLt))

/-- The colour class of `i` in `[0, N]`, as a set of integers. -/
def cl {N : ℕ} (ω : Fin (N + 1) → Fin k) (i : Fin k) : Finset ℤ :=
  (univ.filter fun j => ω j = i).image fun j : Fin (N + 1) => ((j : ℕ) : ℤ)

theorem natCast_mem_cl {N n : ℕ} {ω : Fin (N + 1) → Fin k} {i : Fin k} (hn : n ≤ N)
    (h : ω (pt N n) = i) : ((n : ℕ) : ℤ) ∈ cl ω i :=
  mem_image.2 ⟨pt N n, mem_filter.2 ⟨mem_univ _, h⟩, by rw [pt_val hn]⟩

theorem exists_of_mem_cl {N : ℕ} {ω : Fin (N + 1) → Fin k} {i : Fin k} {x : ℤ}
    (hx : x ∈ cl ω i) : ∃ n : ℕ, n ≤ N ∧ (n : ℤ) = x ∧ ω (pt N n) = i := by
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
  refine ⟨j.val, Nat.lt_succ_iff.1 j.isLt, rfl, ?_⟩
  rw [pt_fin]
  exact (mem_filter.1 hj).2

theorem add_mem_cl {N x y : ℕ} {ω : Fin (N + 1) → Fin k} {i : Fin k} (hx : x ≤ N) (hy : y ≤ N)
    (hcx : ω (pt N x) = i) (hcy : ω (pt N y) = i) :
    ((x + y : ℕ) : ℤ) ∈ cl ω i + cl ω i := by
  have := Finset.add_mem_add (natCast_mem_cl hx hcx) (natCast_mem_cl hy hcy)
  push_cast
  exact this

theorem cl_subset {N : ℕ} (ω : Fin (N + 1) → Fin k) (i : Fin k) :
    cl ω i ⊆ Icc (0 : ℤ) N := by
  intro x hx
  obtain ⟨n, hn, rfl, -⟩ := exists_of_mem_cl hx
  rw [mem_Icc]
  constructor <;> omega

/-! ### The fringe set -/

/-- The `j`-th fringe position: `j` for `j < T`, else `N + 1 - 2T + j`. -/
def fpos (N T j : ℕ) : ℕ := if j < T then j else N + 1 - 2 * T + j

/-- Colourings agreeing with `F` on both fringes. -/
def Omega (N T : ℕ) (F : ℤ → Fin k) : Finset (Fin (N + 1) → Fin k) :=
  univ.filter fun ω => ∀ j < 2 * T,
    ω (pt N (fpos N T j)) ∈ ({F (fpos N T j)} : Finset (Fin k))

theorem omega_left {N T : ℕ} {F : ℤ → Fin k} {ω : Fin (N + 1) → Fin k} (hω : ω ∈ Omega N T F)
    {n : ℕ} (hn : n < T) : ω (pt N n) = F n := by
  have := (mem_filter.1 hω).2 n (by omega)
  simp only [fpos, hn, ite_true, mem_singleton] at this
  exact this

theorem omega_right {N T : ℕ} {F : ℤ → Fin k} {ω : Fin (N + 1) → Fin k} (hω : ω ∈ Omega N T F)
    (hNT : 2 * T ≤ N + 1) {n : ℕ} (hn1 : N < n + T) (hn2 : n ≤ N) : ω (pt N n) = F n := by
  have := (mem_filter.1 hω).2 (n + 2 * T - (N + 1)) (by omega)
  have hf : fpos N T (n + 2 * T - (N + 1)) = n := by
    unfold fpos
    split_ifs with hj <;> omega
  rw [hf, mem_singleton] at this
  exact this

theorem omega_free {N T : ℕ} (F : ℤ → Fin k) {n : ℕ} (hn1 : T ≤ n) (hn2 : n + T ≤ N) :
    Free (Omega N T F) (pt N n) := by
  intro ω hω a
  rw [Omega, mem_filter] at hω ⊢
  refine ⟨mem_univ _, fun j hj => ?_⟩
  have hne : pt N (fpos N T j) ≠ pt N n := by
    apply pt_ne
    · unfold fpos; split_ifs <;> omega
    · omega
    · unfold fpos; split_ifs <;> omega
  rw [Function.update_of_ne hne]
  exact hω.2 j hj

theorem omega_card {N T : ℕ} (F : ℤ → Fin k) (hNT : 2 * T ≤ N + 1) :
    #(Omega N T F) * k ^ (2 * T) = k ^ (N + 1) := by
  have h := card_iter_single k 1 (Fintype.card_fin k) (univ : Finset (Fin (N + 1) → Fin k))
    (2 * T) (fun j => pt N (fpos N T j)) (fun j => {F (fpos N T j)}) (fun _ => card_singleton _)
    (by
      intro j hj j' hj' hne
      apply pt_ne
      · unfold fpos; split_ifs <;> omega
      · unfold fpos; split_ifs <;> omega
      · unfold fpos; split_ifs <;> omega)
    (fun _ _ => free_univ _)
  rw [one_pow, mul_one, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-! ### Deterministic sums from a periodic fringe -/

/-- An interval of `p` consecutive integers contains every residue class mod `p`. -/
theorem residue_in_interval (lo : ℤ) {p : ℕ} (hp : 0 < p) (u : ℤ) :
    ∃ x, lo ≤ x ∧ x < lo + p ∧ x ≡ u [ZMOD p] := by
  refine ⟨lo + (u - lo) % p, ?_, ?_, ?_⟩
  · have := Int.emod_nonneg (u - lo) (by omega : (p : ℤ) ≠ 0)
    omega
  · have := Int.emod_lt_of_pos (u - lo) (by omega : (0 : ℤ) < p)
    omega
  · have h := Int.mod_modEq (u - lo) p
    have := Int.ModEq.add_left lo h
    simpa using this

/-- **Deterministic low sums.**  If the left fringe `[0, T - 1]` is coloured by `G`, `G` is
`p`-periodic and every residue `s` is a sum of two residues of colour `i`, then
`[p - 1, 2T - p - 1] ⊆ cl ω i + cl ω i`. -/
theorem det_low {N T p : ℕ} (G : ℤ → Fin k) (hp : 0 < p) (hpT : p ≤ T) (hTN : T ≤ N)
    (hper : ∀ x y, x ≡ y [ZMOD p] → G x = G y)
    (hrep : ∀ i s, ∃ u, G u = i ∧ G (s - u) = i)
    (ω : Fin (N + 1) → Fin k) (hω : ∀ n < T, ω (pt N n) = G n) (i : Fin k)
    (s : ℕ) (hs1 : p ≤ s + 1) (hs2 : s + p + 1 ≤ 2 * T) :
    (s : ℤ) ∈ cl ω i + cl ω i := by
  obtain ⟨u, hu1, hu2⟩ := hrep i s
  have hlo : ∃ lo : ℤ, 0 ≤ lo ∧ (s : ℤ) - T + 1 ≤ lo ∧ lo + p ≤ s + 1 ∧ lo + p ≤ T := by
    by_cases hsT : s + 1 ≤ T
    · exact ⟨0, le_rfl, by omega, by omega, by omega⟩
    · exact ⟨s - T + 1, by omega, le_rfl, by omega, by omega⟩
  obtain ⟨lo, hlo0, hlo1, hlo2, hlo3⟩ := hlo
  obtain ⟨x, hx1, hx2, hx3⟩ := residue_in_interval lo hp u
  have hx0 : 0 ≤ x := by omega
  set xn := x.toNat with hxn
  have hxx : (xn : ℤ) = x := Int.toNat_of_nonneg hx0
  have hxs : xn ≤ s := by omega
  have hxT : xn < T := by omega
  have hyT : s - xn < T := by omega
  have hcx : ω (pt N xn) = i := by
    rw [hω xn hxT, ← hu1]
    apply hper
    rw [hxx]
    exact hx3
  have hcy : ω (pt N (s - xn)) = i := by
    rw [hω (s - xn) hyT, ← hu2]
    apply hper
    have : ((s - xn : ℕ) : ℤ) = (s : ℤ) - x := by
      rw [Nat.cast_sub hxs, hxx]
    rw [this]
    exact Int.ModEq.sub_left _ hx3
  have := add_mem_cl (by omega) (by omega) hcx hcy
  rwa [Nat.add_sub_cancel' hxs] at this

/-! ### Missing differences -/

/-- **Difference deficit.**  Let `p = 2h`, `T = Q p ≤ N`, and let `F` be `p`-periodic with
`F (x + h) ≠ F x`.  If `ω` agrees with `F` on both fringes then every class misses the `2Q`
differences `± (d₀ - j p)`, `j < Q`, where `d₀ = N - ((N - h) mod p)`. -/
theorem card_sub_cl_le {N T Q h : ℕ} (F : ℤ → Fin k) (hh : 0 < h) (hT : T = Q * (2 * h))
    (hTN : 2 * T ≤ N)
    (hper : ∀ x y, x ≡ y [ZMOD (2 * h : ℕ)] → F x = F y) (hanti : ∀ x, F (x + h) ≠ F x)
    (ω : Fin (N + 1) → Fin k) (hω : ω ∈ Omega N T F) (i : Fin k) :
    #(cl ω i - cl ω i) + 2 * Q ≤ 2 * N + 1 := by
  set p : ℕ := 2 * h with hpdef
  have hp : (0 : ℤ) < p := by omega
  set e : ℤ := ((N : ℤ) - h) % p with he
  have he0 : 0 ≤ e := Int.emod_nonneg _ hp.ne'
  have he1 : e < p := Int.emod_lt_of_pos _ hp
  let d : ℕ → ℤ := fun j => (N : ℤ) - e - j * p
  have hdmod : ∀ j, d j ≡ h [ZMOD p] := by
    intro j
    have h1 : e ≡ (N : ℤ) - h [ZMOD p] := Int.mod_modEq _ _
    have h2 : (j : ℤ) * p ≡ 0 [ZMOD p] := by
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_mul_left _ _
    have := Int.ModEq.sub (Int.ModEq.sub (Int.ModEq.refl (N : ℤ)) h1) h2
    simp only [d]
    convert this using 1
    ring
  have hTq : (T : ℤ) = Q * p := by rw [hT]; push_cast; ring
  have hdlo : ∀ j < Q, (N : ℤ) - T + 1 ≤ d j := by
    intro j hj
    have : (j : ℤ) + 1 ≤ Q := by exact_mod_cast hj
    have : ((j : ℤ) + 1) * p ≤ Q * p := mul_le_mul_of_nonneg_right this hp.le
    simp only [d]
    nlinarith
  have hdhi : ∀ j, d j ≤ N := by
    intro j
    simp only [d]
    have : (0 : ℤ) ≤ j * p := by positivity
    linarith
  -- a difference `d ≥ N - T + 1` with `d ≡ h` is not in `cl - cl`
  have key : ∀ (a b : ℤ), a ∈ cl ω i → b ∈ cl ω i → (N : ℤ) - T + 1 ≤ a - b →
      ¬ (a - b ≡ h [ZMOD p]) := by
    intro a b ha hb hab hmod
    obtain ⟨na, hna, rfl, hca⟩ := exists_of_mem_cl ha
    obtain ⟨nb, hnb, rfl, hcb⟩ := exists_of_mem_cl hb
    have hFa : ω (pt N na) = F na := omega_right hω (by omega) (by omega) hna
    have hFb : ω (pt N nb) = F nb := omega_left hω (by omega)
    have : F (na : ℤ) = F ((nb : ℤ) + h) := by
      apply hper
      have h1 : (nb : ℤ) + ((na : ℤ) - nb) ≡ (nb : ℤ) + h [ZMOD p] := Int.ModEq.add_left _ hmod
      simpa using h1
    exact hanti nb (by rw [← this, ← hFa, hca, ← hcb, hFb])
  -- the set of missing differences
  let D : Finset ℤ := (range Q).image d ∪ (range Q).image fun j => -d j
  have hdinj : Function.Injective d := by
    intro a b hab
    simp only [d] at hab
    have : (a : ℤ) * p = b * p := by linarith
    exact_mod_cast mul_right_cancel₀ hp.ne' this
  have hD : #D = 2 * Q := by
    rw [card_union_of_disjoint]
    · rw [card_image_of_injective _ hdinj, card_image_of_injective _
        (fun a b hab => hdinj (neg_injective hab)), card_range]
      ring
    · rw [disjoint_left]
      intro z hz1 hz2
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hz1
      obtain ⟨b, hb, hb'⟩ := mem_image.1 hz2
      have h1 := hdlo a (mem_range.1 ha)
      have h2 := hdlo b (mem_range.1 hb)
      have : (N : ℤ) - T + 1 ≥ 1 := by omega
      linarith
  have hsub : cl ω i - cl ω i ⊆ Icc (-(N : ℤ)) N \ D := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.1 hz
    have ha' := mem_Icc.1 (cl_subset ω i ha)
    have hb' := mem_Icc.1 (cl_subset ω i hb)
    rw [mem_sdiff, mem_Icc]
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    intro hzD
    rcases mem_union.1 hzD with h1 | h1
    · obtain ⟨j, hj, hjz⟩ := mem_image.1 h1
      exact key a b ha hb (by rw [← hjz]; exact hdlo j (mem_range.1 hj))
        (by rw [← hjz]; exact hdmod j)
    · obtain ⟨j, hj, hjz⟩ := mem_image.1 h1
      have hba : b - a = d j := by linarith
      exact key b a hb ha (by rw [hba]; exact hdlo j (mem_range.1 hj))
        (by rw [hba]; exact hdmod j)
  have hDsub : D ⊆ Icc (-(N : ℤ)) N := by
    intro z hz
    rw [mem_Icc]
    rcases mem_union.1 hz with h1 | h1
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 h1
      have := hdlo j (mem_range.1 hj)
      have := hdhi j
      constructor <;> linarith
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 h1
      have := hdlo j (mem_range.1 hj)
      have := hdhi j
      constructor <;> linarith
  have h1 := card_le_card hsub
  rw [card_sdiff_of_subset hDsub, hD, Int.card_Icc] at h1
  have h2 : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h2, Int.toNat_natCast] at h1
  have h3 : 2 * Q ≤ 2 * N + 1 := by
    have := card_le_card hDsub
    rw [hD, Int.card_Icc, h2, Int.toNat_natCast] at this
    exact this
  omega

/-- If the sumset covers `[p - 1, 2N - p + 1]` then it has at least `2N - 2p + 3` elements. -/
theorem card_add_ge {N p : ℕ} (A : Finset ℤ) (hp : 1 ≤ p) (hpN : p ≤ N)
    (h : ∀ s : ℕ, p ≤ s + 1 → s + p ≤ 2 * N + 1 → (s : ℤ) ∈ A + A) :
    2 * N + 3 ≤ #(A + A) + 2 * p := by
  have hsub : Icc ((p : ℤ) - 1) (2 * N - p + 1) ⊆ A + A := by
    intro z hz
    rw [mem_Icc] at hz
    have hz0 : 0 ≤ z := by omega
    have := h z.toNat (by omega) (by omega)
    rwa [Int.toNat_of_nonneg hz0] at this
  have := card_le_card hsub
  rw [Int.card_Icc] at this
  omega

end Mstd340121
```

## MstdEvents.lean

```lean
import MstdInterval

/-!
# Probability bounds for the missing sums near the lower end

Let `S` be a set of colourings of `[0, N]` whose members colour the left fringe `[0, T - 1]`
by `G`, and which is free at every middle position `n ∈ [T, N - T]`.

* `trans_bad`: for `2T - p ≤ s < 3T`, the colourings with `s ∉ cl ω i + cl ω i` are at most a
  fraction `((k - 1)/k)^(Q - 1)` of `S`: the `Q - 1` fringe points `j p + e` of colour `i`
  give `Q - 1` distinct middle partners `s - (j p + e)`, none of which may have colour `i`.
* `mid_bad`: for `3T ≤ s ≤ N`, with `n = (s - 2T)/2`, the `n` disjoint middle pairs
  `(T + j, s - T - j)` give the fraction `((k^2 - 1)/k^2)^n`.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset Pointwise

variable {k : ℕ}

theorem trans_bad {N T p Q : ℕ} (G : ℤ → Fin k) (hp : 0 < p) (hT : T = Q * p) (hN : 4 * T ≤ N)
    (hper : ∀ x y, x ≡ y [ZMOD p] → G x = G y)
    (hrep : ∀ i s, ∃ u, G u = i ∧ G (s - u) = i)
    (S : Finset (Fin (N + 1) → Fin k)) (hS : ∀ ω ∈ S, ∀ n < T, ω (pt N n) = G n)
    (hfree : ∀ n, T ≤ n → n + T ≤ N → Free S (pt N n))
    (i : Fin k) (s : ℕ) (hs1 : 2 * T ≤ s + p) (hs2 : s < 3 * T) :
    #(S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) * k ^ (Q - 1) ≤ #S * (k - 1) ^ (Q - 1) := by
  obtain ⟨u, hu, -⟩ := hrep i 0
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  set e : ℕ := (u % p).toNat with he
  have he0 : 0 ≤ u % p := Int.emod_nonneg _ hp'.ne'
  have he1 : u % p < p := Int.emod_lt_of_pos _ hp'
  have hee : (e : ℤ) = u % p := Int.toNat_of_nonneg he0
  have hep : e < p := by omega
  have hGe : ∀ j : ℕ, G ((j * p + e : ℕ) : ℤ) = i := by
    intro j
    rw [← hu]
    apply hper
    push_cast
    rw [hee]
    have h1 : (j : ℤ) * p + u % p ≡ 0 + u % p [ZMOD p] := by
      apply Int.ModEq.add_right
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_mul_left _ _
    rw [zero_add] at h1
    exact h1.trans (Int.mod_modEq u p)
  -- `j p + e ≤ T - p - 1` for `j ≤ Q - 2`
  have hjb : ∀ j, j < Q - 1 → j * p + e + p + 1 ≤ T := by
    intro j hj
    have : (j + 1) * p ≤ (Q - 1) * p := Nat.mul_le_mul_right _ (by omega)
    have h2 : (Q - 1) * p + p = T := by
      rw [hT]
      have hQ : 1 ≤ Q := by omega
      calc (Q - 1) * p + p = (Q - 1 + 1) * p := by ring
        _ = Q * p := by rw [Nat.sub_add_cancel hQ]
    nlinarith
  let Y : ℕ → Fin (N + 1) := fun j => pt N (s - (j * p + e))
  have hcount := card_iter_single k (k - 1) (Fintype.card_fin k) S (Q - 1) Y
    (fun _ => univ.erase i)
    (fun _ => by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin])
    (by
      intro j hj j' hj' hne
      have h1 := hjb j hj
      have h2 := hjb j' hj'
      have hne' : j * p ≠ j' * p := fun h => hne (Nat.eq_of_mul_eq_mul_right hp h)
      apply pt_ne (by omega) (by omega)
      omega)
    (by
      intro j hj
      have h1 := hjb j hj
      exact hfree _ (by omega) (by omega))
  have hsub : (S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) ⊆
      S.filter fun ω => ∀ j < Q - 1, ω (Y j) ∈ univ.erase i := by
    intro ω hω
    rw [mem_filter] at hω ⊢
    refine ⟨hω.1, fun j hj => ?_⟩
    rw [mem_erase]
    refine ⟨fun hcol => hω.2 ?_, mem_univ _⟩
    have h1 := hjb j hj
    have hx : ω (pt N (j * p + e)) = i := by
      rw [hS ω hω.1 _ (by omega)]
      exact hGe j
    have := add_mem_cl (N := N) (by omega) (by omega) hx hcol
    rwa [Nat.add_sub_cancel' (by omega)] at this
  calc #(S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) * k ^ (Q - 1)
      ≤ #(S.filter fun ω => ∀ j < Q - 1, ω (Y j) ∈ univ.erase i) * k ^ (Q - 1) :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ = #S * (k - 1) ^ (Q - 1) := hcount

theorem mid_bad {N T : ℕ} (hk : 1 ≤ k) (S : Finset (Fin (N + 1) → Fin k))
    (hfree : ∀ n, T ≤ n → n + T ≤ N → Free S (pt N n))
    (i : Fin k) (s : ℕ) (hs1 : 3 * T ≤ s) (hs2 : s ≤ N) :
    #(S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) * k ^ (2 * ((s - 2 * T) / 2)) ≤
      #S * (k ^ 2 - 1) ^ ((s - 2 * T) / 2) := by
  set n := (s - 2 * T) / 2 with hn
  have hn2 : 2 * n ≤ s - 2 * T := by omega
  let X : ℕ → Fin (N + 1) := fun j => pt N (T + j)
  let Y : ℕ → Fin (N + 1) := fun j => pt N (s - T - j)
  have hcount := card_iter_pair k 1 (by rw [Fintype.card_fin, mul_one]) one_pos hk S n X Y
    (fun _ => {i}) (fun _ => {i}) (fun _ => card_singleton _) (fun _ => card_singleton _)
    (by
      intro j hj j' hj'
      exact pt_ne (by omega) (by omega) (by omega))
    (by
      intro j hj j' hj' hne
      exact pt_ne (by omega) (by omega) (by omega))
    (by
      intro j hj j' hj' hne
      exact pt_ne (by omega) (by omega) (by omega))
    (fun j hj => hfree _ (by omega) (by omega))
    (fun j hj => hfree _ (by omega) (by omega))
  have hsub : (S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) ⊆
      S.filter fun ω => ∀ j < n, ¬(ω (X j) ∈ ({i} : Finset (Fin k)) ∧
        ω (Y j) ∈ ({i} : Finset (Fin k))) := by
    intro ω hω
    rw [mem_filter] at hω ⊢
    refine ⟨hω.1, fun j hj hboth => hω.2 ?_⟩
    rw [mem_singleton, mem_singleton] at hboth
    have := add_mem_cl (N := N) (by omega) (by omega) hboth.1 hboth.2
    rwa [show T + j + (s - T - j) = s by omega] at this
  calc #(S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) * k ^ (2 * n)
      ≤ #(S.filter fun ω => ∀ j < n, ¬(ω (X j) ∈ ({i} : Finset (Fin k)) ∧
          ω (Y j) ∈ ({i} : Finset (Fin k)))) * k ^ (2 * n) :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ = #S * (k ^ 2 - 1) ^ n := hcount

end Mstd340121
```

## MstdReflect.lean

```lean
import MstdInterval

/-!
# Reflection `x ↦ N - x`

Reflecting a colouring of `[0, N]` maps each colour class `A` to `N - A`, hence the sum `s` to
`2N - s`; it maps the fringe set for `F` onto the fringe set for `x ↦ F (N - x)`.  This
transfers the lower-end estimates to the upper end.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset Pointwise

variable {k : ℕ}

/-- The reflected colouring `j ↦ ω (N - j)`. -/
def rev {N : ℕ} (ω : Fin (N + 1) → Fin k) : Fin (N + 1) → Fin k := fun j => ω (Fin.rev j)

theorem rev_pt {N n : ℕ} (hn : n ≤ N) : Fin.rev (pt N n) = pt N (N - n) := by
  apply Fin.ext
  rw [Fin.val_rev, pt_val hn, pt_val (by omega)]
  omega

theorem rev_injective {N : ℕ} : Function.Injective (rev (k := k) (N := N)) := by
  intro ω ω' h
  funext j
  have := congrFun h (Fin.rev j)
  simpa [rev] using this

theorem mem_cl_rev {N : ℕ} (ω : Fin (N + 1) → Fin k) (i : Fin k) (x : ℤ) :
    x ∈ cl (rev ω) i ↔ (N : ℤ) - x ∈ cl ω i := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl, hc⟩ := exists_of_mem_cl hx
    have : ((N - n : ℕ) : ℤ) = (N : ℤ) - n := by rw [Nat.cast_sub hn]
    rw [← this]
    apply natCast_mem_cl (by omega)
    rw [← rev_pt hn]
    exact hc
  · intro hx
    obtain ⟨n, hn, hnx, hc⟩ := exists_of_mem_cl hx
    have hx' : x = ((N - n : ℕ) : ℤ) := by rw [Nat.cast_sub hn]; omega
    rw [hx']
    apply natCast_mem_cl (by omega)
    show ω (Fin.rev (pt N (N - n))) = i
    rw [rev_pt (by omega), show N - (N - n) = n by omega]
    exact hc

/-- `s ∈ A' + A'` for the reflected class iff `2N - s ∈ A + A`. -/
theorem mem_add_cl_rev {N : ℕ} (ω : Fin (N + 1) → Fin k) (i : Fin k) (s : ℤ) :
    s ∈ cl (rev ω) i + cl (rev ω) i ↔ 2 * (N : ℤ) - s ∈ cl ω i + cl ω i := by
  simp only [mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨(N : ℤ) - a, (mem_cl_rev ω i a).1 ha, (N : ℤ) - b, (mem_cl_rev ω i b).1 hb, ?_⟩
    ring
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨(N : ℤ) - a, ?_, (N : ℤ) - b, ?_, by linarith⟩
    · rw [mem_cl_rev, sub_sub_cancel]
      exact ha
    · rw [mem_cl_rev, sub_sub_cancel]
      exact hb

/-- Reflection maps the fringe set for `F` into the fringe set for `x ↦ F (N - x)`. -/
theorem rev_mem_omega {N T : ℕ} (F : ℤ → Fin k) (hNT : 2 * T ≤ N + 1)
    {ω : Fin (N + 1) → Fin k} (hω : ω ∈ Omega N T F) :
    rev ω ∈ Omega N T (fun x => F ((N : ℤ) - x)) := by
  rw [Omega, mem_filter]
  refine ⟨mem_univ _, fun j hj => ?_⟩
  rw [mem_singleton]
  have hf : fpos N T j ≤ N := by unfold fpos; split_ifs <;> omega
  show ω (Fin.rev (pt N (fpos N T j))) = F ((N : ℤ) - (fpos N T j : ℕ))
  rw [rev_pt hf]
  have hcast : ((N - fpos N T j : ℕ) : ℤ) = (N : ℤ) - (fpos N T j : ℕ) := by
    rw [Nat.cast_sub hf]
  rw [← hcast]
  by_cases hjT : j < T
  · have : fpos N T j = j := by simp [fpos, hjT]
    exact omega_right hω hNT (by omega) (by omega)
  · have : fpos N T j = N + 1 - 2 * T + j := by simp [fpos, hjT]
    exact omega_left hω (by omega)

end Mstd340121
```

## MstdUnion.lean

```lean
import MstdEvents
import MstdReflect
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The union bound

Fix `k ≥ 2`, `p = 2h`, a modular colouring `F` (period `p`, antipodally proper, full
modular self-sums), `Q ≥ p` with `Q ≥ 1`, `T = Q p` and `N ≥ 4T`.  With
`ρ = 1 - 1/(2k^2)`, if `2k ((T + p) ρ^(Q-1) + 2k^2 ρ^(T-1)) ≤ 1/2` then at least half of the
colourings in `Omega N T F` have every colour class MSTD.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset Pointwise

variable {k : ℕ}

/-- `ρ = 1 - 1/(2k^2)`. -/
noncomputable def rho (k : ℕ) : ℝ := 1 - 1 / (2 * (k : ℝ) ^ 2)

theorem rho_facts (hk : 2 ≤ k) :
    0 ≤ rho k ∧ rho k < 1 ∧ ((k : ℝ) - 1) / k ≤ rho k ∧
      ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 ≤ rho k ^ 2 ∧ 1 / (1 - rho k) = 2 * (k : ℝ) ^ 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have h1 : 1 / (2 * (k : ℝ) ^ 2) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 0 < 1 / (2 * (k : ℝ) ^ 2) := by positivity
  refine ⟨by unfold rho; linarith, by unfold rho; linarith, ?_, ?_, ?_⟩
  · unfold rho
    rw [div_le_iff₀ hk0]
    have : 1 / (2 * (k : ℝ) ^ 2) * k = 1 / (2 * k) := by field_simp
    have h3 : 1 / (2 * (k : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  · unfold rho
    rw [div_le_iff₀ hk2]
    have : (1 - 1 / (2 * (k : ℝ) ^ 2)) ^ 2 * (k : ℝ) ^ 2 =
        (k : ℝ) ^ 2 - 1 + 1 / (4 * (k : ℝ) ^ 2) := by
      field_simp
      ring
    rw [this]
    have : 0 < 1 / (4 * (k : ℝ) ^ 2) := by positivity
    linarith
  · unfold rho
    field_simp
    ring

/-- From a count `a k^m ≤ b c^m` to a real fraction. -/
theorem nat_to_frac {a b c K m : ℕ} (hK : 0 < K) (h : a * K ^ m ≤ b * c ^ m) :
    (a : ℝ) ≤ b * ((c : ℝ) / K) ^ m := by
  have hKm : (0 : ℝ) < (K : ℝ) ^ m := by positivity
  have h' : (a : ℝ) * (K : ℝ) ^ m ≤ b * (c : ℝ) ^ m := by exact_mod_cast h
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ hKm]
  exact h'

/-- The weight of the sum `s`: the transition bound or the middle bound. -/
noncomputable def W (k T Q s : ℕ) : ℝ := if s < 3 * T then rho k ^ (Q - 1) else rho k ^ (s - (2 * T + 1))

/-- The per-sum estimate for a set `S` with left fringe `G` and free middle. -/
theorem low_bad_le {N T p Q : ℕ} (hk : 2 ≤ k) (G : ℤ → Fin k) (hp : 0 < p) (hT : T = Q * p)
    (hN : 4 * T ≤ N)
    (hper : ∀ x y, x ≡ y [ZMOD p] → G x = G y)
    (hrep : ∀ i s, ∃ u, G u = i ∧ G (s - u) = i)
    (S : Finset (Fin (N + 1) → Fin k)) (hS : ∀ ω ∈ S, ∀ n < T, ω (pt N n) = G n)
    (hfree : ∀ n, T ≤ n → n + T ≤ N → Free S (pt N n))
    (i : Fin k) (s : ℕ) (hs1 : 2 * T ≤ s + p) (hs2 : s ≤ N) :
    (#(S.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i) : ℝ) ≤ #S * W k T Q s := by
  obtain ⟨h0, h1, ha, hb, -⟩ := rho_facts hk
  have hk0 : 0 < k := by omega
  unfold W
  by_cases hs : s < 3 * T
  · simp only [hs, ite_true]
    have := trans_bad G hp hT hN hper hrep S hS hfree i s hs1 hs
    have h2 := nat_to_frac hk0 this
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at h2
    have h3 : (((k : ℝ) - 1) / k) ^ (Q - 1) ≤ rho k ^ (Q - 1) :=
      pow_le_pow_left₀ (div_nonneg (by have : (2:ℝ) ≤ k := (by exact_mod_cast hk); linarith)
        (by positivity)) ha _
    have h4 : (0 : ℝ) ≤ #S := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  · simp only [hs, ite_false]
    rw [not_lt] at hs
    have := mid_bad (by omega) S hfree i s hs hs2
    rw [pow_mul] at this
    have h2 := nat_to_frac (pow_pos hk0 2) this
    have hcast : ((k ^ 2 - 1 : ℕ) : ℝ) = (k : ℝ) ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hk0)]; push_cast; ring
    rw [hcast] at h2
    push_cast at h2
    set n := (s - 2 * T) / 2
    have h3 : (((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2) ^ n ≤ (rho k ^ 2) ^ n :=
      pow_le_pow_left₀ (div_nonneg (by have : (2:ℝ) ≤ k := (by exact_mod_cast hk); nlinarith)
        (by positivity)) hb _
    have h5 : (rho k ^ 2) ^ n ≤ rho k ^ (s - (2 * T + 1)) := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one h0 h1.le (by omega)
    have h4 : (0 : ℝ) ≤ #S := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (h3.trans h5) h4]

/-- The sum of the weights over `s ∈ [2T - p, N]`. -/
theorem sum_W_le {N T p Q : ℕ} (hk : 2 ≤ k) (hpT : p ≤ T) (hT1 : 1 ≤ T) (hN : 3 * T ≤ N) :
    ∑ s ∈ Icc (2 * T - p) N, W k T Q s ≤
      ((T + p : ℕ) : ℝ) * rho k ^ (Q - 1) + 2 * (k : ℝ) ^ 2 * rho k ^ (T - 1) := by
  obtain ⟨h0, h1, -, -, hgeo⟩ := rho_facts hk
  unfold W
  rw [Finset.sum_ite]
  have hA : ∑ _s ∈ (Icc (2 * T - p) N).filter (· < 3 * T), rho k ^ (Q - 1) ≤
      ((T + p : ℕ) : ℝ) * rho k ^ (Q - 1) := by
    rw [sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 _)
    have hsub : (Icc (2 * T - p) N).filter (· < 3 * T) ⊆ Ico (2 * T - p) (3 * T) := by
      intro s hs
      rw [mem_filter, mem_Icc] at hs
      rw [mem_Ico]
      omega
    have := card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast (show #((Icc (2 * T - p) N).filter (· < 3 * T)) ≤ T + p by omega)
  have hB : ∑ s ∈ (Icc (2 * T - p) N).filter (fun s => ¬ s < 3 * T),
      rho k ^ (s - (2 * T + 1)) ≤ 2 * (k : ℝ) ^ 2 * rho k ^ (T - 1) := by
    have hsub : (Icc (2 * T - p) N).filter (fun s => ¬ s < 3 * T) ⊆ Ico (3 * T) (N + 1) := by
      intro s hs
      rw [mem_filter, mem_Icc] at hs
      rw [mem_Ico]
      omega
    calc ∑ s ∈ (Icc (2 * T - p) N).filter (fun s => ¬ s < 3 * T), rho k ^ (s - (2 * T + 1))
        ≤ ∑ s ∈ Ico (3 * T) (N + 1), rho k ^ (s - (2 * T + 1)) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg h0 _)
      _ = ∑ j ∈ Ico (T - 1) (N - 2 * T), rho k ^ j := by
          rw [← show T - 1 + (2 * T + 1) = 3 * T by omega,
            ← show N - 2 * T + (2 * T + 1) = N + 1 by omega,
            ← Finset.sum_Ico_add' (fun s => rho k ^ (s - (2 * T + 1)))]
          refine sum_congr rfl fun j _ => ?_
          rw [Nat.add_sub_cancel]
      _ ≤ rho k ^ (T - 1) / (1 - rho k) := geom_sum_Ico_le_of_lt_one h0 h1
      _ = 2 * (k : ℝ) ^ 2 * rho k ^ (T - 1) := by
          rw [div_eq_mul_one_div, hgeo, mul_comm]
  linarith

end Mstd340121
```

## MstdMain.lean

```lean
import MstdUnion
import MstdModular

/-!
# The labelled theorem

`half_good`: with the parameters of `MstdUnion`, at least half of `Omega N T F` has every class
MSTD.  `exists_Q` chooses `Q`.  `labelled_positive_proportion`: for every `k ≥ 2` there are
`D > 0` and `R` with `k ^ r ≤ D · #(goodColourings r k)` for all `r ≥ R`.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset Pointwise

variable {k : ℕ}

theorem half_good {N T Q h : ℕ} (hk : 2 ≤ k) (F : ℤ → Fin k) (hh : 0 < h)
    (hper : ∀ x y, x ≡ y [ZMOD (2 * h : ℕ)] → F x = F y) (hanti : ∀ x, F (x + h) ≠ F x)
    (hrep : ∀ i s, ∃ u, F u = i ∧ F (s - u) = i)
    (hQ : 2 * h ≤ Q) (hT : T = Q * (2 * h)) (hN : 4 * T ≤ N)
    (hcond : 2 * (k : ℝ) * (((T + 2 * h : ℕ) : ℝ) * rho k ^ (Q - 1) +
      2 * (k : ℝ) ^ 2 * rho k ^ (T - 1)) ≤ 1 / 2) :
    #(Omega N T F) ≤ 2 * #((Omega N T F).filter fun ω => ∀ i, MSTD (cl ω i)) := by
  classical
  set p : ℕ := 2 * h with hpdef
  have hp : 0 < p := by omega
  have hpT : p ≤ T := by rw [hT]; nlinarith
  have hT1 : 1 ≤ T := by omega
  have hNT : 2 * T ≤ N + 1 := by omega
  set Ω := Omega N T F with hΩ
  let F' : ℤ → Fin k := fun x => F ((N : ℤ) - x)
  set Ω' := Omega N T F' with hΩ'
  have hper' : ∀ x y, x ≡ y [ZMOD p] → F' x = F' y := by
    intro x y hxy
    exact hper _ _ (Int.ModEq.sub_left _ hxy)
  have hrep' : ∀ i s, ∃ u, F' u = i ∧ F' (s - u) = i := by
    intro i s
    obtain ⟨u, hu1, hu2⟩ := hrep i (2 * (N : ℤ) - s)
    refine ⟨(N : ℤ) - u, ?_, ?_⟩
    · show F ((N : ℤ) - ((N : ℤ) - u)) = i
      rw [sub_sub_cancel]
      exact hu1
    · show F ((N : ℤ) - (s - ((N : ℤ) - u))) = i
      rw [show (N : ℤ) - (s - ((N : ℤ) - u)) = 2 * (N : ℤ) - s - u by ring]
      exact hu2
  have hper0 : ∀ x y, x ≡ y [ZMOD p] → F x = F y := hper
  -- the bad events
  let low : Fin k → ℕ → Finset (Fin (N + 1) → Fin k) := fun i s =>
    Ω.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i
  let up : Fin k → ℕ → Finset (Fin (N + 1) → Fin k) := fun i s =>
    Ω.filter fun ω => 2 * (N : ℤ) - s ∉ cl ω i + cl ω i
  let low' : Fin k → ℕ → Finset (Fin (N + 1) → Fin k) := fun i s =>
    Ω'.filter fun ω => (s : ℤ) ∉ cl ω i + cl ω i
  let E : Finset (Fin k × ℕ) := (univ : Finset (Fin k)) ×ˢ Icc (2 * T - p) N
  set Bad := Ω.filter fun ω => ¬ ∀ i, MSTD (cl ω i) with hBad
  -- covering
  have hcover : Bad ⊆ E.biUnion fun is => low is.1 is.2 ∪ up is.1 is.2 := by
    intro ω hω
    rw [hBad, mem_filter] at hω
    obtain ⟨hωΩ, hbad⟩ := hω
    rw [not_forall] at hbad
    obtain ⟨i, hi⟩ := hbad
    by_contra hno
    apply hi
    have hin : ∀ s ∈ Icc (2 * T - p) N, (s : ℤ) ∈ cl ω i + cl ω i ∧
        2 * (N : ℤ) - s ∈ cl ω i + cl ω i := by
      intro s hs
      have hmem : (i, s) ∈ E := mem_product.2 ⟨mem_univ _, hs⟩
      have hnot : ω ∉ low i s ∪ up i s := fun h' => hno (mem_biUnion.2 ⟨(i, s), hmem, h'⟩)
      rw [mem_union, not_or] at hnot
      constructor
      · by_contra h1
        exact hnot.1 (mem_filter.2 ⟨hωΩ, h1⟩)
      · by_contra h1
        exact hnot.2 (mem_filter.2 ⟨hωΩ, h1⟩)
    have hall : ∀ s : ℕ, p ≤ s + 1 → s + p ≤ 2 * N + 1 → (s : ℤ) ∈ cl ω i + cl ω i := by
      intro s hs1 hs2
      by_cases hA : s + p + 1 ≤ 2 * T
      · exact det_low F hp hpT (by omega) hper0 hrep ω
          (fun n hn => omega_left hωΩ hn) i s hs1 hA
      by_cases hB : s ≤ N
      · exact (hin s (mem_Icc.2 ⟨by omega, hB⟩)).1
      by_cases hC : s + 2 * T ≤ 2 * N + p
      · have := (hin (2 * N - s) (mem_Icc.2 ⟨by omega, by omega⟩)).2
        have hc : 2 * (N : ℤ) - ((2 * N - s : ℕ) : ℤ) = s := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rwa [hc] at this
      · have hrevΩ := rev_mem_omega F hNT hωΩ
        have := det_low F' hp hpT (by omega) hper' hrep' (rev ω)
          (fun n hn => omega_left hrevΩ hn) i (2 * N - s) (by omega) (by omega)
        rw [mem_add_cl_rev] at this
        have hc : 2 * (N : ℤ) - ((2 * N - s : ℕ) : ℤ) = s := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rwa [hc] at this
    have hc1 := card_add_ge (cl ω i) (by omega) (by omega) hall
    have hc2 := card_sub_cl_le F hh hT (by omega) hper hanti ω hωΩ i
    unfold MSTD
    omega
  -- reflected events
  have hup : ∀ i s, #(up i s) ≤ #(low' i s) := by
    intro i s
    refine card_le_card_of_injOn rev ?_ (rev_injective.injOn)
    intro ω hω
    rw [mem_coe, mem_filter] at hω ⊢
    refine ⟨rev_mem_omega F hNT hω.1, ?_⟩
    rw [mem_add_cl_rev]
    exact hω.2
  have hcardΩ : #Ω' = #Ω := by
    have h1 := omega_card F hNT
    have h2 := omega_card F' hNT
    rw [← hΩ] at h1
    rw [← hΩ'] at h2
    have hk2 : 0 < k ^ (2 * T) := by positivity
    exact Nat.eq_of_mul_eq_mul_right hk2 (h2.trans h1.symm)
  have hlow : ∀ i, ∀ s ∈ Icc (2 * T - p) N, (#(low i s) : ℝ) ≤ #Ω * W k T Q s := by
    intro i s hs
    rw [mem_Icc] at hs
    exact low_bad_le hk F hp hT hN hper0 hrep Ω (fun ω hω n hn => omega_left hω hn)
      (fun n hn1 hn2 => omega_free F hn1 hn2) i s (by omega) hs.2
  have hlow' : ∀ i, ∀ s ∈ Icc (2 * T - p) N, (#(low' i s) : ℝ) ≤ #Ω * W k T Q s := by
    intro i s hs
    rw [mem_Icc] at hs
    rw [← hcardΩ]
    exact low_bad_le hk F' hp hT hN hper' hrep' Ω' (fun ω hω n hn => omega_left hω hn)
      (fun n hn1 hn2 => omega_free F' hn1 hn2) i s (by omega) hs.2
  have hW := sum_W_le (N := N) (Q := Q) hk hpT hT1 (by omega)
  have hbadR : (#Bad : ℝ) ≤ #Ω / 2 := by
    have h1 : (#Bad : ℝ) ≤ ∑ is ∈ E, ((#(low is.1 is.2) : ℝ) + #(up is.1 is.2)) := by
      have := (card_le_card hcover).trans card_biUnion_le
      have h2 : ∑ is ∈ E, #(low is.1 is.2 ∪ up is.1 is.2) ≤
          ∑ is ∈ E, (#(low is.1 is.2) + #(up is.1 is.2)) :=
        sum_le_sum fun is _ => card_union_le _ _
      have h3 := this.trans h2
      exact_mod_cast h3
    have h2 : ∑ is ∈ E, ((#(low is.1 is.2) : ℝ) + #(up is.1 is.2)) ≤
        ∑ is ∈ E, 2 * (#Ω : ℝ) * W k T Q is.2 := by
      apply sum_le_sum
      intro is his
      have hs := (mem_product.1 his).2
      have a1 := hlow is.1 is.2 hs
      have a2 := hlow' is.1 is.2 hs
      have a3 : (#(up is.1 is.2) : ℝ) ≤ #(low' is.1 is.2) := by exact_mod_cast hup _ _
      linarith
    have h3 : ∑ is ∈ E, 2 * (#Ω : ℝ) * W k T Q is.2 =
        2 * (#Ω : ℝ) * (k * ∑ s ∈ Icc (2 * T - p) N, W k T Q s) := by
      rw [← Finset.mul_sum, Finset.sum_product]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hΩ0 : (0 : ℝ) ≤ #Ω := by positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have h4 : 2 * (#Ω : ℝ) * (k * ∑ s ∈ Icc (2 * T - p) N, W k T Q s) ≤
        (#Ω : ℝ) * (2 * (k : ℝ) * (((T + p : ℕ) : ℝ) * rho k ^ (Q - 1) +
          2 * (k : ℝ) ^ 2 * rho k ^ (T - 1))) := by
      have := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 2 * #Ω * k by positivity)
      calc 2 * (#Ω : ℝ) * (k * ∑ s ∈ Icc (2 * T - p) N, W k T Q s)
          = 2 * #Ω * k * ∑ s ∈ Icc (2 * T - p) N, W k T Q s := by ring
        _ ≤ 2 * #Ω * k * (((T + p : ℕ) : ℝ) * rho k ^ (Q - 1) +
            2 * (k : ℝ) ^ 2 * rho k ^ (T - 1)) := this
        _ = (#Ω : ℝ) * (2 * (k : ℝ) * (((T + p : ℕ) : ℝ) * rho k ^ (Q - 1) +
            2 * (k : ℝ) ^ 2 * rho k ^ (T - 1))) := by ring
    have h5 : (#Ω : ℝ) * (2 * (k : ℝ) * (((T + p : ℕ) : ℝ) * rho k ^ (Q - 1) +
          2 * (k : ℝ) ^ 2 * rho k ^ (T - 1))) ≤ #Ω * (1 / 2) :=
      mul_le_mul_of_nonneg_left hcond hΩ0
    linarith
  have hsplit : #(Ω.filter fun ω => ∀ i, MSTD (cl ω i)) + #Bad = #Ω :=
    card_filter_add_card_filter_not (s := Ω) (fun ω => ∀ i, MSTD (cl ω i))
  have hbadN : 2 * #Bad ≤ #Ω := by
    have : (2 * #Bad : ℝ) ≤ #Ω := by linarith
    exact_mod_cast this
  omega

/-- Choice of `Q`. -/
theorem exists_Q (hk : 2 ≤ k) (p : ℕ) (hp : 1 ≤ p) :
    ∃ Q, p ≤ Q ∧ 1 ≤ Q ∧ 2 * (k : ℝ) * (((Q * p + p : ℕ) : ℝ) * rho k ^ (Q - 1) +
      2 * (k : ℝ) ^ 2 * rho k ^ (Q * p - 1)) ≤ 1 / 2 := by
  obtain ⟨h0, h1, -, -, -⟩ := rho_facts hk
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set C : ℝ := 4 * k * (3 * p + 2 * (k : ℝ) ^ 2) with hC
  have hCpos : 0 < C := by positivity
  have hε : 0 < 1 / C := by positivity
  have t1 := tendsto_self_mul_const_pow_of_lt_one h0 h1
  have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  obtain ⟨M, hM⟩ := (((t1.eventually (gt_mem_nhds hε)).and (t2.eventually (gt_mem_nhds hε))).and
    (Filter.eventually_ge_atTop p)).exists
  obtain ⟨⟨hM1, hM2⟩, hM3⟩ := hM
  refine ⟨M + 1, by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel]
  have hpow : rho k ^ ((M + 1) * p - 1) ≤ rho k ^ M := by
    apply pow_le_pow_of_le_one h0 h1.le
    have : M + 1 ≤ (M + 1) * p := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcast : (((M + 1) * p + p : ℕ) : ℝ) = (M : ℝ) * p + 2 * p := by push_cast; ring
  rw [hcast]
  have hρM : 0 ≤ rho k ^ M := pow_nonneg h0 M
  have hk0 : (0 : ℝ) < k := by linarith
  have hb1 : 2 * (k : ℝ) ^ 2 * rho k ^ ((M + 1) * p - 1) ≤ 2 * (k : ℝ) ^ 2 * rho k ^ M :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hb2 : ((M : ℝ) * p + 2 * p) * rho k ^ M = p * ((M : ℝ) * rho k ^ M) + 2 * p * rho k ^ M := by
    ring
  have hM1' : (M : ℝ) * rho k ^ M < 1 / C := hM1
  have hM2' : rho k ^ M < 1 / C := hM2
  have hsum : ((M : ℝ) * p + 2 * p) * rho k ^ M + 2 * (k : ℝ) ^ 2 * rho k ^ M ≤
      (3 * p + 2 * (k : ℝ) ^ 2) * (1 / C) := by
    rw [hb2]
    have hp0 : (0 : ℝ) ≤ p := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hM1'.le hp0, mul_le_mul_of_nonneg_left hM2'.le hp0]
  have hfin : 2 * (k : ℝ) * ((3 * p + 2 * (k : ℝ) ^ 2) * (1 / C)) = 1 / 2 := by
    rw [hC]
    field_simp
    ring
  have h2k : (0 : ℝ) ≤ 2 * k := by positivity
  calc 2 * (k : ℝ) * (((M : ℝ) * p + 2 * p) * rho k ^ M +
        2 * (k : ℝ) ^ 2 * rho k ^ ((M + 1) * p - 1))
      ≤ 2 * (k : ℝ) * (((M : ℝ) * p + 2 * p) * rho k ^ M + 2 * (k : ℝ) ^ 2 * rho k ^ M) := by
        apply mul_le_mul_of_nonneg_left _ h2k
        linarith
    _ ≤ 2 * (k : ℝ) * ((3 * p + 2 * (k : ℝ) ^ 2) * (1 / C)) :=
        mul_le_mul_of_nonneg_left hsum h2k
    _ = 1 / 2 := hfin

theorem cls_eq_image {N : ℕ} (ω : Fin (N + 1) → Fin k) (i : Fin k) :
    cls ω i = (cl ω i).image fun x => x + 1 := by
  unfold cls cl
  rw [image_image]
  rfl

/-- **Labelled positive proportion.**  For every `k ≥ 2` there are `D > 0` and `R` such that
for all `r ≥ R`, `k ^ r ≤ D · #{c : Fin r → Fin k | every colour class is MSTD}`. -/
theorem labelled_positive_proportion : LabelledPositiveProportion := by
  intro k hk
  obtain ⟨h, hodd, F, hper, hanti, hrep⟩ := exists_modular hk
  have hh : 0 < h := hodd.pos
  obtain ⟨Q, hQp, hQ1, hcond⟩ := exists_Q hk (2 * h) (by omega)
  set T := Q * (2 * h) with hT
  refine ⟨2 * k ^ (2 * T), 4 * T + 1, by positivity, ?_⟩
  intro r hr
  obtain ⟨N, rfl⟩ : ∃ N, r = N + 1 := ⟨r - 1, by omega⟩
  have hN : 4 * T ≤ N := by omega
  have hcond' : 2 * (k : ℝ) * (((T + 2 * h : ℕ) : ℝ) * rho k ^ (Q - 1) +
      2 * (k : ℝ) ^ 2 * rho k ^ (T - 1)) ≤ 1 / 2 := hcond
  have hhalf := half_good hk F hh hper hanti hrep hQp hT hN hcond'
  have hcard := omega_card F (show 2 * T ≤ N + 1 by omega)
  have hsub : ((Omega N T F).filter fun ω => ∀ i, MSTD (cl ω i)) ⊆ goodColourings (N + 1) k := by
    intro ω hω
    rw [mem_filter] at hω
    rw [goodColourings, mem_filter]
    refine ⟨mem_univ _, fun i => ?_⟩
    rw [cls_eq_image, mstd_image_add_iff]
    exact hω.2 i
  have h1 := card_le_card hsub
  calc k ^ (N + 1) = #(Omega N T F) * k ^ (2 * T) := hcard.symm
    _ ≤ 2 * #((Omega N T F).filter fun ω => ∀ i, MSTD (cl ω i)) * k ^ (2 * T) :=
        Nat.mul_le_mul_right _ hhalf
    _ ≤ 2 * #(goodColourings (N + 1) k) * k ^ (2 * T) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ = 2 * k ^ (2 * T) * #(goodColourings (N + 1) k) := by ring

end Mstd340121
```

## MstdPartition.lean

```lean
import MstdMain
import Mathlib.Data.Fintype.BigOperators

/-!
# From labelled colourings to unordered partitions

* `card_allPartitions_le`: `#{partitions of Fin r into k blocks} ≤ k ^ r`, via the colouring
  that labels each block by its rank (blocks ordered by their least element).
* `card_goodColourings_le`: `#goodColourings ≤ k ^ k · #goodPartitions`, via
  `c ↦ (partition into colour classes, rank of each colour class)`.
* `conjecture15Count`, `conjecture15`: Conjecture 1.5 of Chu–Luntzlara–Miller–Shao.
-/

set_option linter.unusedSectionVars false

namespace Mstd340121

open Finset Pointwise

variable {r k : ℕ}

/-- The rank of a block among the blocks of `P`, ordered by least element. -/
def rank (P : Finpartition (univ : Finset (Fin r))) (t : Finset (Fin r)) : ℕ :=
  #(P.parts.filter fun u => u.min < t.min)

theorem rank_lt (P : Finpartition (univ : Finset (Fin r))) {t : Finset (Fin r)}
    (ht : t ∈ P.parts) : rank P t < #P.parts := by
  unfold rank
  have hsub : (P.parts.filter fun u => u.min < t.min) ⊆ P.parts.erase t := by
    intro u hu
    rw [mem_filter] at hu
    exact mem_erase.2 ⟨fun h => lt_irrefl _ (h ▸ hu.2), hu.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem ht] at this
  have := card_pos.2 ⟨t, ht⟩
  omega

theorem min_ne_of_parts (P : Finpartition (univ : Finset (Fin r))) {t u : Finset (Fin r)}
    (ht : t ∈ P.parts) (hu : u ∈ P.parts) (hne : t ≠ u) : t.min ≠ u.min := by
  intro h
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty (P.nonempty_of_mem_parts ht)
  have hat : a ∈ t := Finset.mem_of_min ha
  have hau : a ∈ u := Finset.mem_of_min (h ▸ ha)
  exact hne (P.eq_of_mem_parts ht hu hat hau)

theorem rank_injOn (P : Finpartition (univ : Finset (Fin r))) {t u : Finset (Fin r)}
    (ht : t ∈ P.parts) (hu : u ∈ P.parts) (h : rank P t = rank P u) : t = u := by
  by_contra hne
  have hmin := min_ne_of_parts P ht hu hne
  have key : ∀ t u, t ∈ P.parts → u ∈ P.parts → t.min < u.min → rank P t < rank P u := by
    intro t u ht hu hlt
    unfold rank
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨t, mem_filter.2 ⟨ht, hlt⟩, fun h' => lt_irrefl _ (mem_filter.1 h').2⟩
    · intro v hv
      rw [mem_filter] at hv ⊢
      exact ⟨hv.1, hv.2.trans hlt⟩
  rcases lt_or_gt_of_ne hmin with hlt | hlt
  · exact absurd h (key t u ht hu hlt).ne
  · exact absurd h (key u t hu ht hlt).ne'

/-- The colouring labelling each element by the rank of its block. -/
def rankColouring (hk : 1 ≤ k) (P : Finpartition (univ : Finset (Fin r))) : Fin r → Fin k :=
  fun x => ⟨min (rank P (P.part x)) (k - 1), by omega⟩

theorem card_allPartitions_le (hk : 1 ≤ k) : #(allPartitions r k) ≤ k ^ r := by
  have h := card_le_card_of_injOn (s := allPartitions r k) (t := (univ : Finset (Fin r → Fin k)))
    (rankColouring hk) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  · rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    exact h
  intro P hP P' hP' heq
  rw [mem_coe, allPartitions, mem_filter] at hP hP'
  have hrk : ∀ (Q : Finpartition (univ : Finset (Fin r))), #Q.parts = k → ∀ x,
      ((rankColouring hk Q x : Fin k) : ℕ) = rank Q (Q.part x) := by
    intro Q hQ x
    have := rank_lt Q (Q.part_mem.2 (mem_univ x))
    simp only [rankColouring]
    omega
  have hsame : ∀ (Q : Finpartition (univ : Finset (Fin r))), #Q.parts = k → ∀ x y,
      Q.part y = Q.part x ↔ rankColouring hk Q y = rankColouring hk Q x := by
    intro Q hQ x y
    constructor
    · intro h
      apply Fin.ext
      rw [hrk Q hQ, hrk Q hQ, h]
    · intro h
      have := congrArg Fin.val h
      rw [hrk Q hQ, hrk Q hQ] at this
      exact rank_injOn Q (Q.part_mem.2 (mem_univ _)) (Q.part_mem.2 (mem_univ _)) this
  have hpart : ∀ x, P.part x = P'.part x := by
    intro x
    ext y
    rw [P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _),
      P'.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _), hsame P hP.2, hsame P' hP'.2, heq]
  apply Finpartition.ext
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
    rw [← P.part_eq_of_mem ht hx, hpart x]
    exact P'.part_mem.2 (mem_univ x)
  · intro ht
    obtain ⟨x, hx⟩ := P'.nonempty_of_mem_parts ht
    rw [← P'.part_eq_of_mem ht hx, ← hpart x]
    exact P.part_mem.2 (mem_univ x)

/-- The colour class of `i` as a subset of `Fin r`. -/
def fib (c : Fin r → Fin k) (i : Fin k) : Finset (Fin r) := univ.filter fun j => c j = i

open Classical in
/-- The partition of `Fin r` into the colour classes of `c`. -/
noncomputable def toPartition (c : Fin r → Fin k) : Finpartition (univ : Finset (Fin r)) :=
  Finpartition.ofSetoid (Setoid.ker c)

theorem toPartition_parts (c : Fin r → Fin k) (hc : Function.Surjective c) :
    (toPartition c).parts = univ.image (fib c) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx⟩ := (toPartition c).nonempty_of_mem_parts ht
    rw [mem_image]
    refine ⟨c x, mem_univ _, ?_⟩
    rw [← (toPartition c).part_eq_of_mem ht hx]
    ext y
    rw [fib, mem_filter, toPartition, Finpartition.mem_part_ofSetoid_iff_rel]
    simp only [mem_univ, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · intro ht
    obtain ⟨i, -, rfl⟩ := mem_image.1 ht
    obtain ⟨x, hx⟩ := hc i
    have : (toPartition c).part x = fib c i := by
      ext y
      rw [fib, mem_filter, toPartition, Finpartition.mem_part_ofSetoid_iff_rel]
      simp only [mem_univ, true_and]
      rw [← hx]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [← this]
    exact (toPartition c).part_mem.2 (mem_univ x)

theorem fib_injective (c : Fin r → Fin k) (hc : Function.Surjective c) :
    Function.Injective (fib c) := by
  intro i j h
  obtain ⟨x, hx⟩ := hc i
  have : x ∈ fib c j := by rw [← h, fib, mem_filter]; exact ⟨mem_univ _, hx⟩
  rw [fib, mem_filter] at this
  rw [← hx, this.2]

theorem surjective_of_good {c : Fin r → Fin k} (hc : c ∈ goodColourings r k) :
    Function.Surjective c := by
  intro i
  rw [goodColourings, mem_filter] at hc
  have hm := hc.2 i
  by_contra hno
  push Not at hno
  have : cls c i = ∅ := by
    rw [cls, image_eq_empty, filter_eq_empty_iff]
    exact fun j _ => hno j
  rw [MSTD, this] at hm
  simp at hm

theorem toPartition_good {c : Fin r → Fin k} (hc : c ∈ goodColourings r k) :
    toPartition c ∈ goodPartitions r k := by
  have hs := surjective_of_good hc
  rw [goodPartitions, mem_filter]
  refine ⟨mem_univ _, ?_, ?_⟩
  · rw [toPartition_parts c hs, card_image_of_injective _ (fib_injective c hs), card_univ,
      Fintype.card_fin]
  · intro t ht
    rw [toPartition_parts c hs, mem_image] at ht
    obtain ⟨i, -, rfl⟩ := ht
    rw [goodColourings, mem_filter] at hc
    have := hc.2 i
    unfold cls at this
    exact this

theorem card_goodColourings_le :
    #(goodColourings r k) ≤ k ^ k * #(goodPartitions r k) := by
  classical
  let f : (Fin r → Fin k) → Finpartition (univ : Finset (Fin r)) × (Fin k → ℕ) :=
    fun c => (toPartition c, fun i => rank (toPartition c) (fib c i))
  let tgt := (goodPartitions r k) ×ˢ Fintype.piFinset fun _ : Fin k => range k
  have h := card_le_card_of_injOn (s := goodColourings r k) (t := tgt) f ?_ ?_
  · rw [card_product, Fintype.card_piFinset, prod_const, card_range, card_univ,
      Fintype.card_fin] at h
    rw [mul_comm]
    exact h
  · intro c hc
    rw [mem_coe] at hc ⊢
    have hs := surjective_of_good hc
    have hgood := toPartition_good hc
    refine mem_product.2 ⟨hgood, Fintype.mem_piFinset.2 fun i => ?_⟩
    rw [mem_range]
    have hmem : fib c i ∈ (toPartition c).parts := by
      rw [toPartition_parts c hs]
      exact mem_image_of_mem _ (mem_univ i)
    have := rank_lt _ hmem
    rw [goodPartitions, mem_filter] at hgood
    rw [hgood.2.1] at this
    exact this
  · intro c hc c' hc' heq
    rw [mem_coe] at hc hc'
    have hs := surjective_of_good hc
    have hs' := surjective_of_good hc'
    have hP : toPartition c = toPartition c' := congrArg Prod.fst heq
    have hR : ∀ i, rank (toPartition c) (fib c i) = rank (toPartition c') (fib c' i) :=
      fun i => congrFun (congrArg Prod.snd heq) i
    have hfib : ∀ i, fib c i = fib c' i := by
      intro i
      have h1 : fib c i ∈ (toPartition c).parts := by
        rw [toPartition_parts c hs]; exact mem_image_of_mem _ (mem_univ i)
      have h2 : fib c' i ∈ (toPartition c).parts := by
        rw [hP, toPartition_parts c' hs']; exact mem_image_of_mem _ (mem_univ i)
      apply rank_injOn _ h1 h2
      rw [hR i, hP]
    funext x
    have : x ∈ fib c' (c x) := by rw [← hfib]; simp [fib]
    simp only [fib, mem_filter, mem_univ, true_and] at this
    exact this.symm

/-- **Conjecture 1.5, counting form**: `#all ≤ D · #good` for all large `r`. -/
theorem conjecture15Count : Conjecture15Count := by
  intro k hk
  obtain ⟨D, R, hD, hR⟩ := labelled_positive_proportion k hk
  refine ⟨D * k ^ k, R, by positivity, fun r hr => ?_⟩
  calc #(allPartitions r k) ≤ k ^ r := card_allPartitions_le (by omega)
    _ ≤ D * #(goodColourings r k) := hR r hr
    _ ≤ D * (k ^ k * #(goodPartitions r k)) := Nat.mul_le_mul_left _ card_goodColourings_le
    _ = D * k ^ k * #(goodPartitions r k) := by ring

/-- **Conjecture 1.5 (Chu–Luntzlara–Miller–Shao), proportion form.** -/
theorem conjecture15 : Conjecture15 := by
  intro k hk
  obtain ⟨D, R, hD, hR⟩ := conjecture15Count k hk
  obtain ⟨D', R', hD', hR'⟩ := labelled_positive_proportion k hk
  refine ⟨1 / D, by positivity, max R R', fun r hr => ?_⟩
  have h1 := hR r (le_of_max_le_left hr)
  have h2 := hR' r (le_of_max_le_right hr)
  have hgoodC : 0 < #(goodColourings r k) := by
    have : 0 < k ^ r := by positivity
    rcases Nat.eq_zero_or_pos #(goodColourings r k) with h0 | h0
    · rw [h0, mul_zero] at h2; omega
    · exact h0
  have hgoodP : 0 < #(goodPartitions r k) := by
    have := card_goodColourings_le (r := r) (k := k)
    rcases Nat.eq_zero_or_pos #(goodPartitions r k) with h0 | h0
    · rw [h0, mul_zero] at this; omega
    · exact h0
  have hsub : goodPartitions r k ⊆ allPartitions r k := by
    intro P hP
    rw [goodPartitions, mem_filter] at hP
    rw [allPartitions, mem_filter]
    exact ⟨hP.1, hP.2.1⟩
  have hall : 0 < #(allPartitions r k) := lt_of_lt_of_le hgoodP (card_le_card hsub)
  have hallR : (0 : ℚ) < #(allPartitions r k) := by exact_mod_cast hall
  have hDR : (0 : ℚ) < D := by exact_mod_cast hD
  rw [div_le_div_iff₀ hDR hallR, one_mul]
  have : ((#(allPartitions r k) : ℕ) : ℚ) ≤ ((D * #(goodPartitions r k) : ℕ) : ℚ) := by
    exact_mod_cast h1
  push_cast at this
  linarith

end Mstd340121
```

## MstdAxioms.lean

```lean
import MstdPartition

/-!
# Endpoint statements and axiom audit for MathDB 340121

The two endpoints below restate, with every definition unfolded to Mathlib notions, the
reviewer's required forms: the labelled form over all colourings `Fin r → Fin k` and the
literal form over `Finpartition`s of `Fin r` with exactly `k` parts.  Blocks are placed on
`{1, …, r}` by `j ↦ j + 1`, and `MSTD A` is `(A - A).card < (A + A).card` with pointwise
`Finset` operations on `ℤ`.
-/

open Finset Pointwise Mstd340121

theorem mathdb_340121_labelled :
    ∀ k : ℕ, 2 ≤ k → ∃ D R : ℕ, 0 < D ∧ ∀ r : ℕ, R ≤ r →
      k ^ r ≤ D * (univ.filter fun c : Fin r → Fin k => ∀ i : Fin k,
        (((univ.filter fun j => c j = i).image fun j : Fin r => (j : ℤ) + 1) -
          ((univ.filter fun j => c j = i).image fun j : Fin r => (j : ℤ) + 1)).card <
        (((univ.filter fun j => c j = i).image fun j : Fin r => (j : ℤ) + 1) +
          ((univ.filter fun j => c j = i).image fun j : Fin r => (j : ℤ) + 1)).card).card :=
  labelled_positive_proportion

theorem mathdb_340121 :
    ∀ k : ℕ, 2 ≤ k → ∃ D R : ℕ, 0 < D ∧ ∀ r : ℕ, R ≤ r →
      (univ.filter fun P : Finpartition (univ : Finset (Fin r)) => P.parts.card = k).card ≤
        D * (univ.filter fun P : Finpartition (univ : Finset (Fin r)) =>
          P.parts.card = k ∧ ∀ s ∈ P.parts,
            ((s.image fun j : Fin r => (j : ℤ) + 1) - (s.image fun j : Fin r => (j : ℤ) + 1)).card <
            ((s.image fun j : Fin r => (j : ℤ) + 1) + (s.image fun j : Fin r => (j : ℤ) + 1)).card).card :=
  conjecture15Count

#print MSTD
#print cls
#print goodColourings
#print place
#print allPartitions
#print goodPartitions
#print Conjecture15
#print Conjecture15Count
#print LabelledPositiveProportion
#check @exists_modular
#check @card_iter_pair
#check @card_iter_single
#check @card_sub_cl_le
#check @det_low
#check @trans_bad
#check @mid_bad
#check @half_good
#check @card_allPartitions_le
#check @card_goodColourings_le
#check @labelled_positive_proportion
#check @conjecture15Count
#check @conjecture15
#check @mathdb_340121_labelled
#check @mathdb_340121

#print axioms exists_modular
#print axioms half_good
#print axioms labelled_positive_proportion
#print axioms conjecture15Count
#print axioms conjecture15
#print axioms mathdb_340121_labelled
#print axioms mathdb_340121
```

