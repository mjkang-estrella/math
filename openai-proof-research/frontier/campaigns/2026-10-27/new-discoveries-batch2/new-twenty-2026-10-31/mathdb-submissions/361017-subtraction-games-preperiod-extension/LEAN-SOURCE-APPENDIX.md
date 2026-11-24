# Lean source appendix (MathDB 361017)

Modules are listed in import order. Each block is byte-identical to src/<Module>.lean (checked by build_appendix.py --check).

### `SubtractionDefs.lean`

```lean
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Subtraction games with a seed (Miklós–Post, arXiv:2312.02426, Sections 2 and 2.1)

Definitions transcribed from the source.

* Recurrence (1): `w(n) = 1` if `w(n - x) = 0` for some `x ∈ A`, and `w(n) = 0` if `w(n - x) = 1` for all
  `x ∈ A`; it is applied for `n ≥ 0`.
* Definition 3: the seed `S = v⃗(0) = ⟨w(-α), …, w(-1)⟩` gives `w(n)` for `n ∈ [-α, 0)`.  A seed shorter than
  needed "is presumed to be preceded by infinitely many 1's".  So `S i = w(i - α)` for `i : Fin α`, and
  `w(j) = 1` for `j < -α`.
* Definition 2: `{w(n)}` is periodic over `p` if there is `N ∈ ℕ` with `w(n) = w(n + p)` for all `n ≥ N`; the
  period is the least such `p` (positive) and the preperiod the least such `N` (for `p` the period).
* Definition 4: `b ∈ ℕ \ A` is an extension of `(A, S)` if `w_{A ∪ {b}, S} = w_{A, S}`.

`true` encodes the value `1` (a win for the player to move) and `false` the value `0`.
-/

namespace Subtraction

/-- The seed value `w(j)` at a negative position `j` (Definition 3): `S = ⟨w(-α), …, w(-1)⟩`, so
`w(j) = S (j + α)` for `-α ≤ j < 0`, and `w(j) = 1` further left (the seed is preceded by 1's). -/
def seedVal {α : ℕ} (S : Fin α → Bool) (j : ℤ) : Bool :=
  if h : 0 ≤ j + α ∧ j + α < α then S ⟨(j + α).toNat, by omega⟩ else true

/-- The outcome sequence `w_{A,S}` on `ℤ`: the seed for `j < 0`, recurrence (1) for `j ≥ 0`.
The guard `0 < x` only matters for `0 ∈ A`, which the source excludes (`A ⊂ ℕ⁺`). -/
def w (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) (j : ℤ) : Bool :=
  if _hj : j < 0 then seedVal S j
  else !(decide (∀ x ∈ A, (if _hx : 0 < x then w A S (j - x) else true) = true))
termination_by (j + 1).toNat
decreasing_by all_goals omega

/-- The sequence `{w_{A,S}(n)}_{n=0}^∞`. -/
def seq (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) (n : ℕ) : Bool := w A S n

/-- Definition 2: the sequence `f` is periodic over `p`. -/
def PeriodicOver (f : ℕ → Bool) (p : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n = f (n + p)

/-! ## Basic facts -/

theorem seedVal_of_lt {α : ℕ} (S : Fin α → Bool) {j : ℤ} (hj : j + α < 0) : seedVal S j = true := by
  unfold seedVal; rw [dite_eq_right (by omega)]

theorem w_of_neg (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {j : ℤ} (hj : j < 0) :
    w A S j = seedVal S j := by
  rw [w, dite_eq_left hj]

theorem w_of_nonneg (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {j : ℤ} (hj : 0 ≤ j) :
    w A S j = !(decide (∀ x ∈ A, (if _hx : 0 < x then w A S (j - x) else true) = true)) := by
  rw [w, dite_eq_right (not_lt.mpr hj)]

/-- Recurrence (1), for any `A` (moves `0` are ignored). -/
theorem w_rec' (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {j : ℤ} (hj : 0 ≤ j) :
    w A S j = false ↔ ∀ x ∈ A, 0 < x → w A S (j - x) = true := by
  rw [w_of_nonneg A S hj]
  have e : (∀ x ∈ A, (if _hx : 0 < x then w A S (j - x) else true) = true) ↔
      ∀ x ∈ A, 0 < x → w A S (j - x) = true := by
    refine forall₂_congr fun x _ => ?_
    by_cases hx : 0 < x
    · simp [hx]
    · simp [hx]
  have h1 : ∀ (P : Prop) [Decidable P], ((!decide P) = false ↔ P) := by
    intro P _; by_cases h : P <;> simp [h]
  rw [h1]
  exact e

/-- Recurrence (1) for `A ⊂ ℕ⁺`: `w(j) = 0` iff `w(j - x) = 1` for all `x ∈ A`. -/
theorem w_rec (A : Finset ℕ) (h0 : 0 ∉ A) {α : ℕ} (S : Fin α → Bool) {j : ℤ} (hj : 0 ≤ j) :
    w A S j = false ↔ ∀ x ∈ A, w A S (j - x) = true := by
  rw [w_rec' A S hj]
  refine forall₂_congr fun x hx => ?_
  have : 0 < x := Nat.pos_of_ne_zero fun h => h0 (h ▸ hx)
  simp [this]

theorem pos_of_mem {A : Finset ℕ} (h0 : 0 ∉ A) {x : ℕ} (hx : x ∈ A) : 0 < x :=
  Nat.pos_of_ne_zero fun h => h0 (h ▸ hx)

theorem bool_eq_of_false_iff {a b : Bool} (h : a = false ↔ b = false) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Block lemma (cf. Lemma 2.13 (iii)–(iv)): if `w(j) = w(j + p)` on a block `[a - M, a)` of length
`M ≥ max A` with `a ≥ 0`, then `w(j) = w(j + p)` for all `j ≥ a - M`. -/
theorem shift_of_block (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {M : ℕ} (hM : ∀ x ∈ A, x ≤ M)
    {a : ℤ} (ha : 0 ≤ a) (p : ℕ)
    (hb : ∀ j : ℤ, a - M ≤ j → j < a → w A S j = w A S (j + p)) :
    ∀ j : ℤ, a - M ≤ j → w A S j = w A S (j + p) := by
  have key : ∀ t : ℕ, ∀ j : ℤ, a - M ≤ j → j < a - M + t → w A S j = w A S (j + p) := by
    intro t
    induction t with
    | zero => intro j h1 h2; omega
    | succ t ih =>
      intro j h1 h2
      by_cases h3 : j < a - M + t
      · exact ih j h1 h3
      by_cases h4 : j < a
      · exact hb j h1 h4
      have hj0 : 0 ≤ j := by omega
      apply bool_eq_of_false_iff
      rw [w_rec' A S hj0, w_rec' A S (by omega)]
      refine forall₂_congr fun x hx => imp_congr_right fun hx0 => ?_
      have hxM := hM x hx
      have e := ih (j - x) (by omega) (by omega)
      rw [e, show j - (x : ℤ) + p = j + p - x by ring]
  intro j hj
  exact key ((j - (a - M)).toNat + 1) j hj (by omega)

/-- Lemma 2.2: the sequence is eventually periodic (pigeonhole on the windows `v⃗(n)`). -/
theorem exists_period (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) :
    ∃ p : ℕ, 0 < p ∧ PeriodicOver (seq A S) p := by
  set M := A.sup id with hMdef
  have hM : ∀ x ∈ A, x ≤ M := fun x hx => Finset.le_sup (f := id) hx
  let f : Fin (2 ^ M + 1) → (Fin M → Bool) := fun n i => w A S ((n : ℤ) - M + (i : ℕ))
  have hcard : Fintype.card (Fin M → Bool) < Fintype.card (Fin (2 ^ M + 1)) := by simp
  obtain ⟨u, v, huv, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have key : ∀ u v : Fin (2 ^ M + 1), u < v → f u = f v →
      ∃ p : ℕ, 0 < p ∧ PeriodicOver (seq A S) p := by
    intro u v huv hf
    have huv' : (u : ℕ) < v := huv
    refine ⟨v - u, by omega, u, ?_⟩
    have hb : ∀ j : ℤ, (u : ℤ) - M ≤ j → j < u → w A S j = w A S (j + ((v - u : ℕ) : ℤ)) := by
      intro j h1 h2
      have hi : (j - (u - M)).toNat < M := by omega
      have := congrFun hf ⟨(j - (u - M)).toNat, hi⟩
      simp only [f] at this
      have e1 : (u : ℤ) - M + (((j - (u - M)).toNat : ℕ) : ℤ) = j := by omega
      have e2 : (v : ℤ) - M + (((j - (u - M)).toNat : ℕ) : ℤ) = j + ((v - u : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub huv'.le]; omega
      rw [e1, e2] at this
      exact this
    have := shift_of_block A S hM (a := (u : ℤ)) (by positivity) (v - u) hb
    intro n hn
    have h := this n (by omega)
    simp only [seq]
    rw [h]; push_cast; rfl
  rcases lt_or_gt_of_ne huv with h | h
  · exact key u v h hf
  · exact key v u h hf.symm

open Classical in
/-- Definition 2 / Definition 3: `Per(A, S)`, the least `p ≥ 1` over which `{w_{A,S}}` is periodic. -/
noncomputable def Per (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) : ℕ :=
  Nat.find (exists_period A S)

theorem Per_spec (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) :
    0 < Per A S ∧ PeriodicOver (seq A S) (Per A S) := by
  classical
  unfold Per
  convert Nat.find_spec (exists_period A S)

theorem exists_preper (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → seq A S n = seq A S (n + Per A S) :=
  (Per_spec A S).2

open Classical in
/-- Definition 2 / Definition 3: `PrePer(A, S)`, the least `N` such that `w(n) = w(n + Per(A,S))` for all
`n ≥ N`. -/
noncomputable def PrePer (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) : ℕ :=
  Nat.find (exists_preper A S)

/-- Definition 4: `b ∈ ℕ \ A` is an extension of `(A, S)` if `w_{A ∪ {b}, S} = w_{A, S}`.  The seed `S` is
used for `A ∪ {b}` as given; if `max (A ∪ {b}) > α` it is preceded by 1's (built into `seedVal`). -/
def IsExt (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) (b : ℕ) : Prop :=
  b ∉ A ∧ seq (insert b A) S = seq A S

/-- Conjecture 2 of Miklós–Post (Section 7): if `|A| ≤ 3`, then for all `S ∈ {0,1}^α` (`α = max A`), with
`p = Per(A,S)`: if `kp + x` is an extension of `A` for all `k ∈ ℕ⁺` and `x ∈ A`, then `PrePer(A,S) = 0`. -/
def Conjecture2 : Prop :=
  ∀ (A : Finset ℕ) (_h0 : 0 ∉ A) (hne : A.Nonempty), A.card ≤ 3 →
    ∀ S : Fin (A.max' hne) → Bool,
      (∀ k : ℕ, 0 < k → ∀ x ∈ A, IsExt A S (k * Per A S + x)) → PrePer A S = 0

end Subtraction
```

### `SubtractionLemmaK.lean`

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Lemma K

Let `|A| ≤ 3` and let `P : ℤ → Bool` be `p`-periodic and satisfy recurrence (1) at every `m ∈ ℤ`.  If
`P(m) = 1` then `P(m + y) = 0` for some `y ∈ A`.

The proof counts over one period.  We first prove it for a function `f` on a finite abelian group `G` and a
set of moves `D ⊆ G` with `|D| ≤ 3` (inclusion–exclusion over three translates), and then take
`G = ZMod p` and `D` = image of `A`.
-/

namespace Subtraction

open Finset

section Group

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem card_filter_add (φ : G → Prop) [DecidablePred φ] (t : G) :
    (univ.filter fun m => φ (m + t)).card = (univ.filter φ).card := by
  apply Finset.card_nbij' (· + t) (· - t)
  · intro a ha; simpa using ha
  · intro a ha; simpa using ha
  · intro a _; simp
  · intro a _; simp

/-- Inclusion–exclusion for three finite sets, in additive form. -/
theorem card_union3 {β : Type*} [DecidableEq β] (U V Z : Finset β) :
    (U ∪ V ∪ Z).card + (U ∩ V).card + (U ∩ Z).card + (V ∩ Z).card =
      U.card + V.card + Z.card + (U ∩ V ∩ Z).card := by
  have h1 := Finset.card_union_add_card_inter (U ∪ V) Z
  have h2 := Finset.card_union_add_card_inter (U ∩ Z) (V ∩ Z)
  have h3 := Finset.card_union_add_card_inter U V
  have e1 : (U ∪ V) ∩ Z = (U ∩ Z) ∪ (V ∩ Z) := Finset.union_inter_distrib_right U V Z
  have e2 : (U ∩ Z) ∩ (V ∩ Z) = U ∩ V ∩ Z := by
    ext a; simp only [Finset.mem_inter]; tauto
  rw [e1] at h1
  rw [e2] at h2
  omega

theorem exists_three_of_card_le {β : Type*} [DecidableEq β] (D : Finset β) (hne : D.Nonempty)
    (hD : D.card ≤ 3) : ∃ a b c : β, D = {a, b, c} := by
  have hpos := hne.card_pos
  interval_cases h : D.card
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, a, b, by simp⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.mp h
    exact ⟨a, b, c, rfl⟩

/-- Lemma K on a finite abelian group. -/
theorem lemmaK_group (D : Finset G) (hD : D.card ≤ 3) (f : G → Bool)
    (hrec : ∀ m, f m = false ↔ ∀ y ∈ D, f (m - y) = true) :
    ∀ m, f m = true → ∃ y ∈ D, f (m + y) = false := by
  -- (i) independence
  have indep : ∀ z, f z = false → ∀ y ∈ D, f (z + y) = true := by
    intro z hz y hy
    by_contra h
    have h' : f (z + y) = false := by simpa using h
    have := (hrec (z + y)).1 h' y hy
    rw [add_sub_cancel_right] at this
    rw [hz] at this
    exact Bool.false_ne_true this
  rcases D.eq_empty_or_nonempty with hDe | hne
  · intro m hm
    have : f m = false := (hrec m).2 (by simp [hDe])
    rw [hm] at this; simp at this
  obtain ⟨a, b, c, rfl⟩ := exists_three_of_card_le D hne hD
  -- translates
  let X : G → Finset G := fun y => univ.filter fun m => f (m - y) = false
  let Y : G → Finset G := fun y => univ.filter fun m => f (m + y) = false
  have memX : ∀ y m, m ∈ X y ↔ f (m - y) = false := by intro y m; simp [X]
  have memY : ∀ y m, m ∈ Y y ↔ f (m + y) = false := by intro y m; simp [Y]
  -- singles
  have single : ∀ y, (X y).card = (Y y).card := by
    intro y
    have := card_filter_add (fun m => f (m - y) = false) (y + y)
    rw [← this]
    congr 1
    ext m
    simp only [mem_filter, mem_univ, true_and, Y]
    rw [show m + (y + y) - y = m + y by abel]
  -- pairs
  have pair : ∀ y z, (X y ∩ X z).card = (Y y ∩ Y z).card := by
    intro y z
    have e : X y ∩ X z = univ.filter fun m => f (m - y) = false ∧ f (m - z) = false := by
      ext m; simp [memX]
    have e' : Y y ∩ Y z = univ.filter fun m => f (m + (y + z) - y) = false ∧
        f (m + (y + z) - z) = false := by
      ext m
      simp only [mem_inter, memY, mem_filter, mem_univ, true_and]
      rw [show m + (y + z) - y = m + z by abel, show m + (y + z) - z = m + y by abel]
      exact And.comm
    rw [e, e']
    exact (card_filter_add (fun m => f (m - y) = false ∧ f (m - z) = false) (y + z)).symm
  -- triple: pointwise inclusion
  have triple : X a ∩ X b ∩ X c ⊆ Y a ∩ Y b ∩ Y c := by
    intro m hm
    simp only [mem_inter, memX] at hm
    obtain ⟨⟨ha, hb⟩, hc⟩ := hm
    have hall : ∀ y' ∈ ({a, b, c} : Finset G), f (m - y') = false := by
      intro y' hy'
      simp only [mem_insert, mem_singleton] at hy'
      rcases hy' with rfl | rfl | rfl <;> assumption
    have key : ∀ y ∈ ({a, b, c} : Finset G), f (m + y) = false := by
      intro y hy
      refine (hrec (m + y)).2 fun y' hy' => ?_
      have := indep (m - y') (hall y' hy') y hy
      rwa [show m - y' + y = m + y - y' by abel] at this
    simp only [mem_inter, memY]
    exact ⟨⟨key a (by simp), key b (by simp)⟩, key c (by simp)⟩
  -- the complement of the zero set
  let T : Finset G := univ.filter fun m => f m = true
  have hR : X a ∪ X b ∪ X c = T := by
    ext m
    simp only [mem_union, memX, T, mem_filter, mem_univ, true_and]
    constructor
    · rintro ((h | h) | h) <;>
      · by_contra hm
        have hm' : f m = false := by simpa using hm
        have := (hrec m).1 hm'
        simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at this
        rw [h] at this
        simp at this
    · intro hm
      by_contra h
      simp only [not_or, Bool.not_eq_false] at h
      have : f m = false := (hrec m).2 (by
        simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
        exact ⟨h.1.1, h.1.2, h.2⟩)
      rw [hm] at this; simp at this
  have hS : Y a ∪ Y b ∪ Y c ⊆ T := by
    intro m hm
    simp only [mem_union, memY] at hm
    simp only [T, mem_filter, mem_univ, true_and]
    by_contra h
    have h' : f m = false := by simpa using h
    rcases hm with (hm | hm) | hm
    · have := indep m h' a (by simp); rw [hm] at this; exact Bool.false_ne_true this
    · have := indep m h' b (by simp); rw [hm] at this; exact Bool.false_ne_true this
    · have := indep m h' c (by simp); rw [hm] at this; exact Bool.false_ne_true this
  -- counting
  have ieX := card_union3 (X a) (X b) (X c)
  have ieY := card_union3 (Y a) (Y b) (Y c)
  have ht := Finset.card_le_card triple
  rw [single a, single b, single c, pair a b, pair a c, pair b c] at ieX
  have hle : T.card ≤ (Y a ∪ Y b ∪ Y c).card := by rw [← hR]; omega
  have heq : Y a ∪ Y b ∪ Y c = T := Finset.eq_of_subset_of_card_le hS hle
  intro m hm
  have hmT : m ∈ T := by simp [T, hm]
  rw [← heq] at hmT
  simp only [mem_union, memY] at hmT
  rcases hmT with (h | h) | h
  · exact ⟨a, by simp, h⟩
  · exact ⟨b, by simp, h⟩
  · exact ⟨c, by simp, h⟩

end Group

/-- The statement of Lemma K for a set of moves `A`. -/
def LemmaKFor (A : Finset ℕ) : Prop :=
  ∀ p : ℕ, 0 < p → ∀ P : ℤ → Bool, (∀ m, P (m + p) = P m) →
    (∀ m, P m = false ↔ ∀ x ∈ A, P (m - x) = true) →
      ∀ m, P m = true → ∃ y ∈ A, P (m + y) = false

theorem periodic_int {p : ℕ} {P : ℤ → Bool} (hper : ∀ m, P (m + p) = P m) :
    ∀ m (k : ℤ), P (m + p * k) = P m := by
  intro m k
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [show m + (p : ℤ) * (k + 1) = m + p * k + p by ring, hper, ih]
  | pred k ih =>
    rw [← ih, ← hper (m + p * (-(k : ℤ) - 1))]
    congr 1; ring

/-- **Lemma K.** For `|A| ≤ 3`, no periodic solution of the recurrence on `ℤ` has a `1` at `m` with `1`s at
all of `m + A`. -/
theorem lemmaK (A : Finset ℕ) (hA : A.card ≤ 3) : LemmaKFor A := by
  intro p hp P hper hrec
  have : NeZero p := ⟨hp.ne'⟩
  let f : ZMod p → Bool := fun z => P (z.val : ℤ)
  have hPf : ∀ m : ℤ, P m = f (m : ZMod p) := by
    intro m
    simp only [f, ZMod.val_intCast]
    have := periodic_int hper (m % p) (m / p)
    rw [Int.emod_def, sub_add_cancel] at this
    rw [Int.emod_def]
    exact this
  have hcast : ∀ z : ZMod p, (((z.val : ℤ)) : ZMod p) = z := by
    intro z; simp
  let D : Finset (ZMod p) := A.image fun x : ℕ => (x : ZMod p)
  have hD : D.card ≤ 3 := (Finset.card_image_le).trans hA
  have hrecf : ∀ z, f z = false ↔ ∀ y ∈ D, f (z - y) = true := by
    intro z
    show P (z.val : ℤ) = false ↔ _
    rw [hrec]
    simp only [D, Finset.forall_mem_image]
    refine forall₂_congr fun x _ => ?_
    rw [hPf]
    push_cast
    simp only [ZMod.natCast_zmod_val]
  intro m hm
  rw [hPf] at hm
  obtain ⟨y, hy, hfy⟩ := lemmaK_group D hD f hrecf (m : ZMod p) hm
  simp only [D, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, hx, ?_⟩
  rw [hPf]
  push_cast
  exact hfy

end Subtraction
```

### `SubtractionMain.lean`

```lean
import SubtractionDefs
import SubtractionLemmaK

/-!
# Conjecture 2 of Miklós–Post

Steps 0–4 of the proof: an extension `p + x` forces zeros to translate backwards by `p` (Steps 0–1); the
periodic part `P` of the sequence is a periodic solution on `ℤ` that dominates the sequence (Step 2); the last
position where `w(n) ≠ w(n + p)` would be a counterexample to Lemma K (Step 4).
-/

namespace Subtraction

/-- Step 0 (easy direction of Proposition 2.8): if `b > 0` is an extension then `w(n) = 0` implies
`w(n - b) = 1` for every `n ≥ 0`. -/
theorem cond_of_isExt (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {b : ℕ} (hb : 0 < b)
    (h : IsExt A S b) : ∀ n : ℤ, 0 ≤ n → w A S n = false → w A S (n - b) = true := by
  have hW : ∀ j : ℤ, w (insert b A) S j = w A S j := by
    intro j
    rcases lt_or_ge j 0 with hj | hj
    · rw [w_of_neg _ S hj, w_of_neg _ S hj]
    · have := congrFun h.2 j.toNat
      simp only [seq] at this
      rwa [Int.toNat_of_nonneg hj] at this
  intro n hn hwn
  rw [← hW n] at hwn
  have := (w_rec' (insert b A) S hn).1 hwn b (Finset.mem_insert_self b A) hb
  rwa [hW] at this

section Main

variable (A : Finset ℕ) (h0 : 0 ∉ A) {α : ℕ} (S : Fin α → Bool)

/-- Iterating a period on `ℤ`. -/
theorem iter_period {p : ℕ} {L : ℤ} (hL : ∀ j : ℤ, L ≤ j → w A S j = w A S (j + p)) :
    ∀ j : ℤ, L ≤ j → ∀ t : ℕ, w A S (j + t * p) = w A S j := by
  intro j hj t
  induction t with
  | zero => simp
  | succ t ih =>
    have := hL (j + t * p) (by have : (0 : ℤ) ≤ t * p := by positivity
                               omega)
    rw [← ih, this]; congr 1; push_cast; ring

include h0 in
/-- Steps 1–4. -/
theorem pure_of_backward (hc : A.card ≤ 3) (p : ℕ) (hp : 0 < p) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → seq A S n = seq A S (n + p))
    (hC : ∀ x ∈ A, ∀ n : ℤ, 0 ≤ n → w A S n = false → w A S (n - (p + x)) = true) :
    ∀ n : ℕ, seq A S n = seq A S (n + p) := by
  set M := A.sup id with hMdef
  have hM : ∀ x ∈ A, x ≤ M := fun x hx => Finset.le_sup (f := id) hx
  -- periodicity on ℤ from `N`
  have hNZ : ∀ j : ℤ, (N : ℤ) ≤ j → w A S j = w A S (j + p) := by
    intro j hj
    have := hN j.toNat (by omega)
    simp only [seq] at this
    rw [Int.toNat_of_nonneg (by omega)] at this
    push_cast at this
    rw [Int.toNat_of_nonneg (by omega)] at this
    exact this
  have hit := iter_period A S hNZ
  -- Step 1: zeros translate backwards
  have step1 : ∀ n : ℤ, 0 ≤ n → w A S (n + p) = false → w A S n = false := by
    intro n hn h
    refine (w_rec A h0 S hn).2 fun x hx => ?_
    have := hC x hx (n + p) (by omega) h
    rwa [show n + (p : ℤ) - ((p : ℤ) + (x : ℤ)) = n - x by ring] at this
  -- Step 2: the periodic part
  let K : ℤ → ℕ := fun m => (N + M - m).toNat
  have hK : ∀ m : ℤ, (N : ℤ) + M ≤ m + K m * p := by
    intro m
    have h1 : ((K m : ℕ) : ℤ) ≤ (K m : ℤ) * p := by
      have : (1 : ℤ) ≤ p := by exact_mod_cast hp
      nlinarith [(Nat.cast_nonneg (K m) : (0 : ℤ) ≤ K m)]
    have h2 : (N : ℤ) + M - m ≤ K m := by simp only [K]; omega
    linarith
  let P : ℤ → Bool := fun m => w A S (m + K m * p)
  have P_eq : ∀ m : ℤ, ∀ k : ℕ, (N : ℤ) ≤ m + k * p → P m = w A S (m + k * p) := by
    intro m k hk
    have h1 := hit (m + K m * p) (by have := hK m; omega) k
    have h2 := hit (m + k * p) hk (K m)
    show w A S (m + K m * p) = w A S (m + k * p)
    rw [← h1, ← h2]; congr 1; ring
  have P_per : ∀ m : ℤ, P (m + p) = P m := by
    intro m
    have hk := hK m
    have hM0 : (0 : ℤ) ≤ M := by positivity
    rw [P_eq (m + p) (K m) (by omega), P_eq m (K m + 1) (by push_cast; nlinarith)]
    congr 1; push_cast; ring
  have P_rec : ∀ m : ℤ, P m = false ↔ ∀ x ∈ A, P (m - x) = true := by
    intro m
    have hk := hK m
    show w A S (m + K m * p) = false ↔ _
    have hN0 : (0 : ℤ) ≤ N := by positivity
    rw [w_rec A h0 S (by omega)]
    refine forall₂_congr fun x hx => ?_
    have hxM : (x : ℤ) ≤ M := by exact_mod_cast hM x hx
    rw [P_eq (m - x) (K m) (by omega), show m + K m * p - x = m - x + K m * p by ring]
  -- (B): zeros of `P` are zeros of `w`
  have hB : ∀ n : ℤ, 0 ≤ n → P n = false → w A S n = false := by
    intro n hn hPn
    have back : ∀ t : ℕ, w A S (n + t * p) = false → w A S n = false := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        intro h
        apply ih
        apply step1 (n + t * p) (by positivity)
        rw [show n + (t : ℤ) * p + p = n + ((t + 1 : ℕ) : ℤ) * p by push_cast; ring]
        exact h
    exact back (K n) hPn
  -- Step 4: the last position where `w(n) ≠ w(n + p)`
  classical
  have hex : ∃ L : ℕ, ∀ n : ℕ, L ≤ n → w A S n = w A S (n + p) := by
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simp only [seq] at this
    rw [this]; push_cast; rfl
  suffices h : Nat.find hex = 0 by
    have := Nat.find_spec hex
    rw [h] at this
    intro n
    simp only [seq]
    rw [this n (Nat.zero_le n)]; push_cast; rfl
  by_contra hne
  obtain ⟨n0, hn0⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hgood : ∀ n : ℕ, n0 + 1 ≤ n → w A S n = w A S (n + p) := by
    have := Nat.find_spec hex; rw [hn0] at this; exact this
  have hbad : w A S n0 ≠ w A S (n0 + p) := by
    have hmin := Nat.find_min hex (show n0 < Nat.find hex by omega)
    push Not at hmin
    obtain ⟨n, hn1, hn2⟩ := hmin
    rcases Nat.lt_or_ge n (n0 + 1) with h | h
    · have : n = n0 := by omega
      subst this; exact hn2
    · exact absurd (hgood n h) hn2
  -- beyond `n0` the sequence agrees with `P`
  have hgoodZ : ∀ j : ℤ, ((n0 + 1 : ℕ) : ℤ) ≤ j → w A S j = w A S (j + p) := by
    intro j hj
    have := hgood j.toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at this
    exact this
  have hWP : ∀ j : ℤ, ((n0 + 1 : ℕ) : ℤ) ≤ j → w A S j = P j := by
    intro j hj
    have hk := hK j
    rw [P_eq j (K j) (by have : (0 : ℤ) ≤ M := by positivity
                         omega)]
    exact (iter_period A S hgoodZ j hj (K j)).symm
  have hnp : w A S ((n0 : ℤ) + p) = P n0 := by
    rw [hWP _ (by push_cast; omega), P_per]
  cases hw : w A S n0 with
  | true =>
    have hP : P n0 = false := by
      rw [← hnp]; rw [hw] at hbad
      cases h : w A S ((n0 : ℤ) + p) with
      | false => rfl
      | true => exact absurd h.symm hbad
    have := hB n0 (by positivity) hP
    rw [hw] at this; exact absurd this (by simp)
  | false =>
    have hP : P n0 = true := by
      rw [← hnp]; rw [hw] at hbad
      cases h : w A S ((n0 : ℤ) + p) with
      | true => rfl
      | false => exact absurd h.symm hbad
    have hy : ∀ y ∈ A, P (n0 + y) = true := by
      intro y hy
      have hy0 := pos_of_mem h0 hy
      rw [← hWP _ (by push_cast; omega)]
      by_contra h
      have h' : w A S (n0 + y) = false := by simpa using h
      have := (w_rec A h0 S (by positivity)).1 h' y hy
      rw [add_sub_cancel_right, hw] at this
      exact absurd this (by simp)
    obtain ⟨y, hyA, hPy⟩ := lemmaK A hc p hp P P_per P_rec n0 hP
    rw [hy y hyA] at hPy
    exact absurd hPy (by simp)

end Main

/-- **Stronger form.** For `0 ∉ A`, `|A| ≤ 3`, any seed, and any eventual period `p ≥ 1` of `w_{A,S}`:
if for every `x ∈ A` the number `p + x` lies in `A` or is an extension of `(A, S)`, then
`w(n) = w(n + p)` for all `n ≥ 0`. -/
theorem pure_of_period (A : Finset ℕ) (h0 : 0 ∉ A) (hc : A.card ≤ 3) {α : ℕ} (S : Fin α → Bool)
    (p : ℕ) (hp : 0 < p) (hper : PeriodicOver (seq A S) p)
    (hext : ∀ x ∈ A, p + x ∈ A ∨ IsExt A S (p + x)) :
    ∀ n : ℕ, seq A S n = seq A S (n + p) := by
  obtain ⟨N, hN⟩ := hper
  refine pure_of_backward A h0 S hc p hp N hN fun x hx n hn hwn => ?_
  rcases hext x hx with hA | hE
  · have := (w_rec A h0 S hn).1 hwn (p + x) hA
    simpa using this
  · have := cond_of_isExt A S (b := p + x) (by have := pos_of_mem h0 hx; omega) hE n hn hwn
    simpa using this

theorem preper_eq_zero_iff (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) :
    PrePer A S = 0 ↔ ∀ n : ℕ, seq A S n = seq A S (n + Per A S) := by
  classical
  unfold PrePer
  rw [Nat.find_eq_zero]
  simp

/-- Conjecture 2 with the hypothesis for `k = 1` only, any seed length. -/
theorem conjecture2_k1 (A : Finset ℕ) (h0 : 0 ∉ A) (hc : A.card ≤ 3) {α : ℕ} (S : Fin α → Bool)
    (hext : ∀ x ∈ A, IsExt A S (Per A S + x)) : PrePer A S = 0 := by
  rw [preper_eq_zero_iff]
  exact pure_of_period A h0 hc S (Per A S) (Per_spec A S).1 (Per_spec A S).2
    fun x hx => Or.inr (hext x hx)

/-- **Conjecture 2 of Miklós–Post** (arXiv:2312.02426, Section 7), as stated. -/
theorem conjecture2 : Conjecture2 := by
  intro A h0 _ hc S hext
  exact conjecture2_k1 A h0 hc S fun x hx => by simpa using hext 1 one_pos x hx

end Subtraction
```

### `SubtractionCompute.lean`

```lean
import SubtractionMain

/-!
# Finite certificates for `Per`, `PrePer` and extensions

A structurally recursive table `wc` of the first values of `w_{A,S}` (proved equal to `w`), the converse
direction of Proposition 2.8, and criteria that reduce `Per(A,S) = p`, `PrePer(A,S) = N₀` and "every
`kp + x` is an extension" to finitely many table look-ups, checked by `decide` in the examples.
-/

namespace Subtraction

/-- Proposition 2.8 (⇐): `b ∉ A`, `b > 0`, and `w(n) = 0 ⟹ w(n - b) = 1` for all `n ≥ 0` make `b` an
extension. -/
theorem isExt_of_cond (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {b : ℕ} (hb : 0 < b) (hbA : b ∉ A)
    (h : ∀ n : ℤ, 0 ≤ n → w A S n = false → w A S (n - b) = true) : IsExt A S b := by
  refine ⟨hbA, ?_⟩
  have key : ∀ t : ℕ, ∀ j : ℤ, j < t → w (insert b A) S j = w A S j := by
    intro t
    induction t with
    | zero =>
      intro j hj
      have hj' : j < 0 := by omega
      rw [w_of_neg _ S hj', w_of_neg _ S hj']
    | succ t ih =>
      intro j hj
      rcases lt_or_ge j t with h1 | h1
      · exact ih j h1
      rcases lt_or_ge j 0 with h2 | h2
      · rw [w_of_neg _ S h2, w_of_neg _ S h2]
      apply bool_eq_of_false_iff
      rw [w_rec' _ S h2, w_rec' _ S h2]
      constructor
      · intro hB x hx hx0
        rw [← ih (j - x) (by omega)]
        exact hB x (Finset.mem_insert_of_mem hx) hx0
      · intro hA x hx hx0
        rw [ih (j - x) (by omega)]
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact h j h2 ((w_rec' A S h2).2 hA)
        · exact hA x hx' hx0
  funext n
  exact key (n + 1) n (by omega)

/-- The first `n` values of the sequence, computed by a structural recursion (for kernel evaluation). -/
def wc (l : List ℕ) {α : ℕ} (S : Fin α → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    wc l S n ++ [!(l.all fun x => if 0 < x then
      (if x ≤ n then (wc l S n).getD (n - x) true else seedVal S ((n : ℤ) - x)) else true)]

theorem wc_eq (A : Finset ℕ) (l : List ℕ) (hl : ∀ x, x ∈ A ↔ x ∈ l) {α : ℕ} (S : Fin α → Bool) :
    ∀ n : ℕ, wc l S n = (List.range n).map fun i : ℕ => w A S (i : ℤ) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wc, ih, List.range_succ, List.map_append, List.map_singleton]
    congr 2
    rw [w_of_nonneg A S (by positivity), List.all_eq]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro H x hx
      have H' := H x ((hl x).1 hx)
      by_cases hx0 : 0 < x
      · rw [dite_eq_left hx0]
        rw [ite_eq_left hx0] at H'
        by_cases hxn : x ≤ n
        · rw [ite_eq_left hxn] at H'
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)] at H'
          simpa [Nat.cast_sub hxn] using H'
        · rw [ite_eq_right hxn] at H'
          rwa [w_of_neg A S (by omega)]
      · rw [dite_eq_right hx0]
    · intro H x hx
      have H' := H x ((hl x).2 hx)
      by_cases hx0 : 0 < x
      · rw [dite_eq_left hx0] at H'
        rw [ite_eq_left hx0]
        by_cases hxn : x ≤ n
        · rw [ite_eq_left hxn]
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
          simpa [Nat.cast_sub hxn] using H'
        · rw [ite_eq_right hxn]
          rwa [w_of_neg A S (by omega)] at H'
      · rw [ite_eq_right hx0]

/-- Look-up of `w(j)` in a table of the first values. -/
def look {α : ℕ} (S : Fin α → Bool) (L : List Bool) (j : ℤ) : Bool :=
  if j < 0 then seedVal S j else L.getD j.toNat true

theorem w_eq_look (A : Finset ℕ) (l : List ℕ) (hl : ∀ x, x ∈ A ↔ x ∈ l) {α : ℕ} (S : Fin α → Bool)
    (B : ℕ) {j : ℤ} (hj : j < B) : w A S j = look S (wc l S B) j := by
  unfold look
  by_cases h : j < 0
  · rw [ite_eq_left h, w_of_neg A S h]
  · rw [ite_eq_right h, wc_eq A l hl S B, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp [Int.toNat_of_nonneg (not_lt.mp h)]

theorem seq_iter {f : ℕ → Bool} {p N0 : ℕ} (h : ∀ n, N0 ≤ n → f n = f (n + p)) :
    ∀ n, N0 ≤ n → ∀ t : ℕ, f (n + t * p) = f n := by
  intro n hn t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← ih, h (n + t * p) (by omega)]
    congr 1; ring

theorem per_eq (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {p N0 : ℕ} (hp : 0 < p)
    (hper : ∀ n, N0 ≤ n → seq A S n = seq A S (n + p))
    (hmin : ∀ q, 0 < q → q < p → ∃ r, N0 ≤ r ∧ seq A S r ≠ seq A S (r + q)) : Per A S = p := by
  classical
  unfold Per
  rw [Nat.find_eq_iff]
  refine ⟨⟨hp, N0, hper⟩, fun q hq ⟨hq0, N, hN⟩ => ?_⟩
  obtain ⟨r, hr, hne⟩ := hmin q hq0 hq
  have e1 := seq_iter hper r hr N
  have e2 := seq_iter hper (r + q) (by omega) N
  have hNp : N ≤ N * p := Nat.le_mul_of_pos_right N hp
  have := hN (r + N * p) (by omega)
  apply hne
  rw [← e1, ← e2, this, show r + N * p + q = r + q + N * p by ring]

theorem preper_eq (A : Finset ℕ) {α : ℕ} (S : Fin α → Bool) {N0 : ℕ}
    (hper : ∀ n, N0 ≤ n → seq A S n = seq A S (n + Per A S))
    (hmin : 0 < N0 → seq A S (N0 - 1) ≠ seq A S (N0 - 1 + Per A S)) : PrePer A S = N0 := by
  classical
  unfold PrePer
  rw [Nat.find_eq_iff]
  exact ⟨hper, fun N hN hall => hmin (by omega) (hall (N0 - 1) (by omega))⟩

/-- Periodicity over `p` from `N₀` from one block of length `M ≥ max A`. -/
theorem periodic_of_check (A : Finset ℕ) (l : List ℕ) (hl : ∀ x, x ∈ A ↔ x ∈ l) {α : ℕ}
    (S : Fin α → Bool) (M B N0 p : ℕ) (hM : ∀ x ∈ A, x ≤ M) (hB : N0 + M + p ≤ B)
    (hchk : ∀ i < M, look S (wc l S B) ((N0 + i : ℕ) : ℤ) = look S (wc l S B) ((N0 + i + p : ℕ) : ℤ)) :
    ∀ n : ℕ, N0 ≤ n → seq A S n = seq A S (n + p) := by
  have hb : ∀ j : ℤ, ((N0 + M : ℕ) : ℤ) - M ≤ j → j < ((N0 + M : ℕ) : ℤ) →
      w A S j = w A S (j + p) := by
    intro j h1 h2
    have hi : (j - N0).toNat < M := by push_cast at h1 h2; omega
    have := hchk _ hi
    have e1 : (((N0 + (j - N0).toNat : ℕ)) : ℤ) = j := by push_cast at h1 h2 ⊢; omega
    have e2 : (((N0 + (j - N0).toNat + p : ℕ)) : ℤ) = j + p := by push_cast at h1 h2 ⊢; omega
    rw [e1, e2] at this
    rw [w_eq_look A l hl S B (by push_cast at h2; omega),
      w_eq_look A l hl S B (j := j + p) (by push_cast at h2; omega)]
    exact this
  have := shift_of_block A S hM (by positivity) p hb
  intro n hn
  have h := this n (by push_cast; omega)
  simp only [seq]; rw [h]; push_cast; rfl

/-- `Per(A,S) = p` and `PrePer(A,S) = N₀` from finitely many table entries. -/
theorem per_preper_of_check (A : Finset ℕ) (l : List ℕ) (hl : ∀ x, x ∈ A ↔ x ∈ l) {α : ℕ}
    (S : Fin α → Bool) (M B N0 p : ℕ) (hM : ∀ x ∈ A, x ≤ M) (hp : 0 < p) (hB : N0 + M + 2 * p ≤ B)
    (hchk : ∀ i < M, look S (wc l S B) ((N0 + i : ℕ) : ℤ) = look S (wc l S B) ((N0 + i + p : ℕ) : ℤ))
    (hmin : ∀ q < p, 0 < q →
      ∃ i < p, look S (wc l S B) ((N0 + i : ℕ) : ℤ) ≠ look S (wc l S B) ((N0 + i + q : ℕ) : ℤ))
    (hpre : N0 = 0 ∨ look S (wc l S B) ((N0 - 1 : ℕ) : ℤ) ≠ look S (wc l S B) ((N0 - 1 + p : ℕ) : ℤ)) :
    Per A S = p ∧ PrePer A S = N0 := by
  have hper := periodic_of_check A l hl S M B N0 p hM (by omega) hchk
  have hseq : ∀ n : ℕ, n < B → seq A S n = look S (wc l S B) n := fun n hn =>
    w_eq_look A l hl S B (by exact_mod_cast hn)
  have hPer : Per A S = p := by
    refine per_eq A S hp hper fun q hq0 hq => ?_
    obtain ⟨i, hi, hne⟩ := hmin q hq hq0
    refine ⟨N0 + i, by omega, ?_⟩
    rw [hseq _ (by omega), hseq _ (by omega)]
    exact hne
  refine ⟨hPer, preper_eq A S (hPer ▸ hper) fun hN0 => ?_⟩
  rcases hpre with h | h
  · omega
  · rw [hPer, hseq _ (by omega), hseq _ (by omega)]
    exact h

/-- Every `kp + x` (`k ≥ 1`, `x ∈ A`) is an extension, from eventual periodicity over `p ≥ N₀ + M` and a
finite check on `[-M, N₀)`. -/
theorem allExt_of_check (A : Finset ℕ) (h0 : 0 ∉ A) {α : ℕ} (S : Fin α → Bool) (M N0 p : ℕ)
    (hM : ∀ x ∈ A, x ≤ M) (hαM : α ≤ M) (hp : N0 + M ≤ p)
    (hper : ∀ n : ℕ, N0 ≤ n → seq A S n = seq A S (n + p))
    (hchk : ∀ x ∈ A, ∀ m : ℤ, -(M : ℤ) ≤ m → m < N0 → w A S (m + x + p) = false → w A S m = true) :
    ∀ k : ℕ, 0 < k → ∀ x ∈ A, IsExt A S (k * p + x) := by
  intro k hk x hx
  have hx0 := pos_of_mem h0 hx
  have hxM := hM x hx
  have hkp : p ≤ k * p := Nat.le_mul_of_pos_left p hk
  have hperZ : ∀ j : ℤ, (N0 : ℤ) ≤ j → w A S j = w A S (j + p) := by
    intro j hj
    have := hper j.toNat (by omega)
    simp only [seq] at this
    rw [Int.toNat_of_nonneg (by omega)] at this
    push_cast at this
    rw [Int.toNat_of_nonneg (by omega)] at this
    exact this
  have hit := iter_period A S hperZ
  refine isExt_of_cond A S (by omega) (fun hb => by have := hM _ hb; omega) fun n hn hwn => ?_
  push_cast
  set m := n - ((k : ℤ) * p + x) with hm
  have hkpZ : (p : ℤ) ≤ (k : ℤ) * p := by exact_mod_cast hkp
  rcases lt_or_ge m (-(M : ℤ)) with h1 | h1
  · rw [w_of_neg A S (by omega), seedVal_of_lt S (by omega)]
  rcases le_or_gt (N0 : ℤ) m with h2 | h2
  · have e := hit m h2 k
    rw [← e, show m + (k : ℤ) * p = n - x by omega]
    exact (w_rec A h0 S hn).1 hwn x hx
  · refine hchk x hx m h1 h2 ?_
    have e := hit (m + x + p) (by omega) (k - 1)
    rw [← e]
    have : m + (x : ℤ) + p + ((k - 1 : ℕ) : ℤ) * p = n := by
      rw [Nat.cast_sub (by omega)]; push_cast; rw [hm]; ring
    rw [this]; exact hwn

/-- Table form of `allExt_of_check`. -/
theorem allExt_of_listcheck (A : Finset ℕ) (l : List ℕ) (hl : ∀ x, x ∈ A ↔ x ∈ l) (h0 : 0 ∉ A)
    {α : ℕ} (S : Fin α → Bool) (M N0 p B : ℕ) (hM : ∀ x ∈ A, x ≤ M) (hαM : α ≤ M) (hp : N0 + M ≤ p)
    (hB : N0 + M + p ≤ B) (hper : ∀ n : ℕ, N0 ≤ n → seq A S n = seq A S (n + p))
    (hchk : ∀ x ∈ l, ∀ i < M + N0,
      look S (wc l S B) ((i : ℤ) - M + x + p) = false → look S (wc l S B) ((i : ℤ) - M) = true) :
    ∀ k : ℕ, 0 < k → ∀ x ∈ A, IsExt A S (k * p + x) := by
  refine allExt_of_check A h0 S M N0 p hM hαM hp hper fun x hx m h1 h2 hw => ?_
  have hxM := hM x hx
  have := hchk x ((hl x).1 hx) (m + M).toNat (by omega)
  rw [show (((m + M).toNat : ℕ) : ℤ) - M = m by omega] at this
  rw [w_eq_look A l hl S B (by omega)]
  rw [w_eq_look A l hl S B (by omega)] at hw
  exact this hw

/-- Changing the seed's index type along `α = β` changes nothing. -/
theorem hyp_cast (A : Finset ℕ) {α β : ℕ} (h : α = β) (S : Fin β → Bool) :
    ((∀ k : ℕ, 0 < k → ∀ x ∈ A,
        IsExt A (fun i : Fin α => S (Fin.cast h i)) (k * Per A (fun i : Fin α => S (Fin.cast h i)) + x)) ↔
      ∀ k : ℕ, 0 < k → ∀ x ∈ A, IsExt A S (k * Per A S + x)) ∧
    PrePer A (fun i : Fin α => S (Fin.cast h i)) = PrePer A S ∧
    Per A (fun i : Fin α => S (Fin.cast h i)) = Per A S := by
  subst h
  exact ⟨Iff.rfl, rfl, rfl⟩

end Subtraction
```

### `SubtractionExamples.lean`

```lean
import SubtractionCompute

/-!
# Non-vacuity and sharpness, checked by kernel evaluation

* `{1,5,6}` with seed `011011`: `Per = 7` (the no-seed period is 11), `PrePer = 0`, and every `7k + x` is an
  extension, so the hypothesis of Conjecture 2 holds (also in the literal form with `S : Fin (max A) → Bool`).
* The source's examples: `{2,4,7}` (no seed) has `Per = 3`, `PrePer = 4`; `{3,5}` with seed `0110` has
  `Per = 8`, `PrePer = 0`, and `11 = 8 + 3` is not an extension (`w_{{3,5,11}}` has period 2 and preperiod 11).
* `|A| = 4`: for `{1,2,6,11}` (no seed) the hypothesis holds but `PrePer = 1`, so the statement fails without
  `|A| ≤ 3`; and Lemma K fails for `{2,5,6,7}` (a 12-periodic solution).
-/

namespace Subtraction.Examples

open Subtraction

/-- The seed `011011`, i.e. `w(-6..-1) = 0,1,1,0,1,1`. -/
def seed156 : Fin 6 → Bool := fun i => [false, true, true, false, true, true].getD i.val true

theorem ex156_per_preper : Per {1, 5, 6} seed156 = 7 ∧ PrePer {1, 5, 6} seed156 = 0 :=
  per_preper_of_check {1, 5, 6} [1, 5, 6] (by intro x; simp) seed156 6 20 0 7 (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ex156_hyp : ∀ k : ℕ, 0 < k → ∀ x ∈ ({1, 5, 6} : Finset ℕ),
    IsExt {1, 5, 6} seed156 (k * Per {1, 5, 6} seed156 + x) := by
  rw [ex156_per_preper.1]
  exact allExt_of_listcheck {1, 5, 6} [1, 5, 6] (by intro x; simp) (by decide) seed156 6 0 7 20
    (by decide) le_rfl (by decide) (by decide)
    (periodic_of_check {1, 5, 6} [1, 5, 6] (by intro x; simp) seed156 6 20 0 7 (by decide) (by decide)
      (by decide +kernel))
    (by decide +kernel)

/-- The hypothesis of `Conjecture2` (all `k ≥ 1`) is satisfiable with `|A| = 3` and a seed of the literal
type `Fin (max A) → Bool` that is not all ones. -/
theorem conjecture2_hypothesis_satisfiable :
    ∃ (A : Finset ℕ) (_ : 0 ∉ A) (hne : A.Nonempty), A.card = 3 ∧ ∃ S : Fin (A.max' hne) → Bool,
      (∃ i, S i = false) ∧ (∀ k : ℕ, 0 < k → ∀ x ∈ A, IsExt A S (k * Per A S + x)) := by
  have hne : ({1, 5, 6} : Finset ℕ).Nonempty := ⟨1, by simp⟩
  have hmax : ({1, 5, 6} : Finset ℕ).max' hne = 6 :=
    le_antisymm (Finset.max'_le _ _ _ (by decide)) (Finset.le_max' _ 6 (by simp))
  refine ⟨{1, 5, 6}, by decide, hne, by decide, fun i => seed156 (Fin.cast hmax i),
    ⟨⟨0, by rw [hmax]; norm_num⟩, rfl⟩, ?_⟩
  exact (hyp_cast _ hmax seed156).1.2 ex156_hyp

/-- Source example (Section 2): `Per({2,4,7}) = 3`, `PrePer({2,4,7}) = 4`. -/
theorem ex247 : Per {2, 4, 7} (fun _ : Fin 7 => true) = 3 ∧ PrePer {2, 4, 7} (fun _ : Fin 7 => true) = 4 :=
  per_preper_of_check {2, 4, 7} [2, 4, 7] (by intro x; simp) _ 7 20 4 3 (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The seed `0110` (shorter than `α = 5`, so preceded by a `1`). -/
def seed0110 : Fin 4 → Bool := fun i => [false, true, true, false].getD i.val true

/-- Source example (Section 2.2): `w_{{3,5},0110} = (01⁵0²)^∞`. -/
theorem ex35 : Per {3, 5} seed0110 = 8 ∧ PrePer {3, 5} seed0110 = 0 :=
  per_preper_of_check {3, 5} [3, 5] (by intro x; simp) seed0110 5 24 0 8 (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Source example: `w_{{3,5,11},0110} = 01⁵01013(01)^∞`, period 2.  The printed non-repeating prefix has
length 12; the preperiod in the sense of Definition 2 is 11, since `w(11) = w(13) = 1`. -/
theorem ex35_11 : Per (insert 11 {3, 5}) seed0110 = 2 ∧ PrePer (insert 11 {3, 5}) seed0110 = 11 :=
  per_preper_of_check (insert 11 {3, 5}) [11, 3, 5] (by intro x; simp) seed0110 11 30 11 2 (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Source example: `11 = Per + 3` is not an extension of `({3,5}, 0110)`. -/
theorem ex35_not_ext : ¬ IsExt {3, 5} seed0110 (Per {3, 5} seed0110 + 3) := by
  rw [ex35.1]
  rintro ⟨-, h⟩
  have := congrFun h 7
  simp only [seq] at this
  rw [w_eq_look (insert (8 + 3) {3, 5}) [11, 3, 5] (by intro x; simp) seed0110 30 (by norm_num),
    w_eq_look {3, 5} [3, 5] (by intro x; simp) seed0110 30 (by norm_num)] at this
  revert this
  decide +kernel

/-- Source counterexample for `|A| = 4`: `{1,2,6,11}`, no seed, `Per = 12`, `PrePer = 1`. -/
theorem ex4 : Per {1, 2, 6, 11} (fun _ : Fin 11 => true) = 12 ∧
    PrePer {1, 2, 6, 11} (fun _ : Fin 11 => true) = 1 :=
  per_preper_of_check {1, 2, 6, 11} [1, 2, 6, 11] (by intro x; simp) _ 11 36 1 12 (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ex4_hyp : ∀ k : ℕ, 0 < k → ∀ x ∈ ({1, 2, 6, 11} : Finset ℕ),
    IsExt {1, 2, 6, 11} (fun _ : Fin 11 => true) (k * Per {1, 2, 6, 11} (fun _ : Fin 11 => true) + x) := by
  rw [ex4.1]
  exact allExt_of_listcheck {1, 2, 6, 11} [1, 2, 6, 11] (by intro x; simp) (by decide) _ 11 1 12 36
    (by decide) le_rfl (by decide) (by decide)
    (periodic_of_check {1, 2, 6, 11} [1, 2, 6, 11] (by intro x; simp) _ 11 36 1 12 (by decide)
      (by decide) (by decide +kernel))
    (by decide +kernel)

/-- The bound `|A| ≤ 3` cannot be replaced by `|A| ≤ 4`. -/
theorem conjecture2_fails_card4 :
    ¬ ∀ (A : Finset ℕ) (_ : 0 ∉ A) (hne : A.Nonempty), A.card ≤ 4 →
      ∀ S : Fin (A.max' hne) → Bool,
        (∀ k : ℕ, 0 < k → ∀ x ∈ A, IsExt A S (k * Per A S + x)) → PrePer A S = 0 := by
  intro H
  have hne : ({1, 2, 6, 11} : Finset ℕ).Nonempty := ⟨1, by simp⟩
  have hmax : ({1, 2, 6, 11} : Finset ℕ).max' hne = 11 :=
    le_antisymm (Finset.max'_le _ _ _ (by decide)) (Finset.le_max' _ 11 (by simp))
  have hc := hyp_cast {1, 2, 6, 11} hmax (fun _ : Fin 11 => true)
  have := H {1, 2, 6, 11} (by decide) hne (by decide) _ (hc.1.2 ex4_hyp)
  rw [hc.2.1, ex4.2] at this
  exact absurd this (by norm_num)

/-- A 12-periodic solution for `A = {2,5,6,7}`: `110111111100`. -/
def cexP (m : ℤ) : Bool :=
  [true, true, false, true, true, true, true, true, true, true, false, false].getD (m % 12).toNat true

/-- Lemma K fails for the 4-element set `{2,5,6,7}`. -/
theorem not_lemmaK_2567 : ¬ LemmaKFor {2, 5, 6, 7} := by
  intro H
  have hmod : ∀ m : ℤ, cexP m = cexP (m % 12) := by
    intro m; simp only [cexP]; rw [show m % 12 % 12 = m % 12 by omega]
  have hper : ∀ m : ℤ, cexP (m + ((12 : ℕ) : ℤ)) = cexP m := by
    intro m; rw [hmod, hmod m, show (m + ((12 : ℕ) : ℤ)) % 12 = m % 12 by omega]
  have hfin : ∀ r : ℕ, r < 12 →
      (cexP r = false ↔ ∀ x ∈ ({2, 5, 6, 7} : Finset ℕ), cexP ((r : ℤ) - x) = true) := by
    decide +kernel
  have hrec : ∀ m : ℤ, cexP m = false ↔ ∀ x ∈ ({2, 5, 6, 7} : Finset ℕ), cexP (m - x) = true := by
    intro m
    have hr := hfin (m % 12).toNat (by omega)
    rw [show (((m % 12).toNat : ℕ) : ℤ) = m % 12 by omega] at hr
    rw [hmod m, hr]
    refine forall₂_congr fun x _ => ?_
    rw [hmod (m % 12 - x), hmod (m - x), show (m % 12 - x) % 12 = (m - x) % 12 by omega]
  obtain ⟨y, hy, h⟩ := H 12 (by norm_num) cexP hper hrec 1 (by decide +kernel)
  have hall : ∀ y ∈ ({2, 5, 6, 7} : Finset ℕ), cexP (1 + y) = true := by decide +kernel
  rw [hall y hy] at h
  exact absurd h (by decide)

end Subtraction.Examples
```

### `SubtractionAudit.lean`

```lean
import SubtractionExamples

/-! Audit: definitions, endpoint statements and axioms. -/

open Subtraction Subtraction.Examples

#print seedVal
#print w
#print seq
#print PeriodicOver
#print Per
#print PrePer
#print IsExt
#print Conjecture2
#print LemmaKFor

#check @conjecture2
#check @conjecture2_k1
#check @pure_of_period
#check @lemmaK
#check @exists_period
#check @conjecture2_hypothesis_satisfiable
#check @ex156_per_preper
#check @conjecture2_fails_card4
#check @ex4
#check @not_lemmaK_2567
#check @ex247
#check @ex35
#check @ex35_11
#check @ex35_not_ext

#print axioms conjecture2
#print axioms conjecture2_k1
#print axioms pure_of_period
#print axioms lemmaK
#print axioms exists_period
#print axioms conjecture2_hypothesis_satisfiable
#print axioms ex156_per_preper
#print axioms ex156_hyp
#print axioms conjecture2_fails_card4
#print axioms ex4
#print axioms ex4_hyp
#print axioms not_lemmaK_2567
#print axioms ex247
#print axioms ex35
#print axioms ex35_11
#print axioms ex35_not_ext
```

