# Lean source appendix (MathDB 347302)

Modules are listed in import order; each fenced block is byte-identical to `src/<Module>.lean` (without its final newline).

### `PathRuns.lean`

```lean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Path combinatorics for the ear `u w₁ … w_p v`

Ear positions are natural numbers: `0` is `u`, `1, …, p` are `w₁, …, w_p`, `p + 1` is `v`.
A set of ear vertices is a `Finset ℕ` contained in `Icc 1 p`; `z : ℕ → ℕ` gives the values
at the positions.  This file proves the interval formulas, the "fill" and "split" lemmas and
the run induction principle (Lemma 2.1(b) of the proof, the run/gap argument).
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Finset

namespace Ear

/-- Prefix sums of `z - 1`: `P z j = ∑_{t=1}^{j} (z t - 1)`. -/
def P (z : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => P z j + (z (j + 1) : ℤ) - 1

@[simp] lemma P_zero (z : ℕ → ℕ) : P z 0 = 0 := rfl
lemma P_succ (z : ℕ → ℕ) (j : ℕ) : P z (j + 1) = P z j + (z (j + 1) : ℤ) - 1 := rfl

/-- `z(S)`. -/
def zs (z : ℕ → ℕ) (S : Finset ℕ) : ℕ := ∑ t ∈ S, z t

lemma zs_Ioc (z : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) :
    (zs z (Ioc i j) : ℤ) = ((j - i : ℕ) : ℤ) + P z j - P z i := by
  induction j, h using Nat.le_induction with
  | base => simp [zs]
  | succ j hij ih =>
    rw [zs, sum_Ioc_succ_top (by omega), Nat.cast_add, ← zs, ih, P_succ]
    push_cast [show j + 1 - i = (j - i) + 1 by omega]
    ring

lemma P_lb (z : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : P z i - ((j - i : ℕ) : ℤ) ≤ P z j := by
  have h1 := zs_Ioc z h
  have h2 : (0 : ℤ) ≤ (zs z (Ioc i j) : ℤ) := Nat.cast_nonneg _
  linarith

/-- The ear part `Ω(σ, S)` of the closed neighbourhood: ear positions adjacent to or in `S`,
together with `w₁` if `u` is selected (`a`) and `w_p` if `v` is selected (`b`). -/
def Om (p : ℕ) (a b : Bool) (S : Finset ℕ) : Finset ℕ :=
  (Icc 1 p).filter
    (fun t => t ∈ S ∨ t + 1 ∈ S ∨ t - 1 ∈ S ∨ (a = true ∧ t = 1) ∨ (b = true ∧ t = p))

/-- The closed neighbourhood of `S` in the path `0, 1, …, p+1`. -/
def NP (p : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (range (p + 2)).filter (fun t => t ∈ S ∨ t + 1 ∈ S ∨ (1 ≤ t ∧ t - 1 ∈ S))

/-- `φ_σ(S) = |Ω(σ,S)| - z(S)`. -/
def phi (p : ℕ) (a b : Bool) (z : ℕ → ℕ) (S : Finset ℕ) : ℤ :=
  ((Om p a b S).card : ℤ) - zs z S

/-- `ψ(S) = |N_P[S]| - z(S)`. -/
def psi (p : ℕ) (z : ℕ → ℕ) (S : Finset ℕ) : ℤ :=
  ((NP p S).card : ℤ) - zs z S

/-! ## Interval formulas -/

lemma Om_Ioc_eq {p i j : ℕ} (a b : Bool) (hij : i < j) (hjp : j ≤ p) :
    Om p a b (Ioc i j) =
      Icc (if 1 ≤ i then i else 1) (if j < p then j + 1 else j) ∪
        ((if a = true ∧ 2 ≤ i then {1} else ∅) ∪ (if b = true ∧ j + 2 ≤ p then {p} else ∅)) := by
  ext t
  simp only [Om, mem_filter, mem_Icc, mem_Ioc, mem_union]
  cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;>
    split_ifs <;> (try simp) <;> omega

lemma card_Om_Ioc {p i j : ℕ} (a b : Bool) (hij : i < j) (hjp : j ≤ p) :
    ((Om p a b (Ioc i j)).card : ℤ) = ((j - i : ℕ) : ℤ) + (if 1 ≤ i then 1 else 0)
      + (if j < p then 1 else 0) + (if a = true ∧ 2 ≤ i then 1 else 0)
      + (if b = true ∧ j + 2 ≤ p then 1 else 0) := by
  have hd1 : Disjoint (if a = true ∧ 2 ≤ i then ({1} : Finset ℕ) else ∅)
      (if b = true ∧ j + 2 ≤ p then {p} else ∅) := by
    cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;>
      (try split_ifs) <;> (try simp) <;> omega
  have hd2 : Disjoint (Icc (if 1 ≤ i then i else 1) (if j < p then j + 1 else j))
      ((if a = true ∧ 2 ≤ i then {1} else ∅) ∪ (if b = true ∧ j + 2 ≤ p then {p} else ∅)) := by
    rw [disjoint_union_right]
    cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;>
      constructor <;> (try split_ifs) <;> (try simp) <;> omega
  rw [Om_Ioc_eq a b hij hjp, card_union_of_disjoint hd2, card_union_of_disjoint hd1, Nat.card_Icc]
  cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte] <;>
    (try split_ifs) <;> (try simp) <;> omega

lemma phi_Ioc {p i j : ℕ} (a b : Bool) (z : ℕ → ℕ) (hij : i < j) (hjp : j ≤ p) :
    phi p a b z (Ioc i j) = (if 1 ≤ i then 1 else 0) + (if j < p then 1 else 0)
      + (if a = true ∧ 2 ≤ i then 1 else 0) + (if b = true ∧ j + 2 ≤ p then 1 else 0)
      - (P z j - P z i) := by
  rw [phi, card_Om_Ioc a b hij hjp, zs_Ioc z hij.le]
  ring

lemma NP_Ioc_eq {p i j : ℕ} (hij : i < j) (hjp : j ≤ p) : NP p (Ioc i j) = Icc i (j + 1) := by
  ext t
  simp only [NP, mem_filter, mem_range, mem_Ioc, mem_Icc]
  omega

lemma psi_Ioc {p i j : ℕ} (z : ℕ → ℕ) (hij : i < j) (hjp : j ≤ p) :
    psi p z (Ioc i j) = 2 - (P z j - P z i) := by
  rw [psi, NP_Ioc_eq hij hjp, Nat.card_Icc, zs_Ioc z hij.le]
  push_cast [show j + 1 + 1 - i = (j - i) + 2 by omega]
  ring

lemma phi_empty (p : ℕ) (a b : Bool) (z : ℕ → ℕ) :
    phi p a b z ∅ = ((Om p a b ∅).card : ℤ) := by
  simp [phi, zs]

/-! ## Fill and split -/

lemma Om_insert {p t : ℕ} (a b : Bool) {S : Finset ℕ} (h1 : t - 1 ∈ S) (h2 : t + 1 ∈ S)
    (ht : 2 ≤ t) : Om p a b (insert t S) = Om p a b S := by
  ext x
  simp only [Om, mem_filter, mem_insert, mem_Icc]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rcases h with (h | h) | (h | h) | (h | h) | h | h
    · subst h; exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inl h
    · left; rw [show x = t - 1 by omega]; exact h1
    · exact Or.inr (Or.inl h)
    · left; rw [show x = t + 1 by omega]; exact h2
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rcases h with h | h | h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

lemma NP_insert {p t : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 p) (h1 : t - 1 ∈ S) (h2 : t + 1 ∈ S)
    (ht : 2 ≤ t) : NP p (insert t S) = NP p S := by
  have h2' := mem_Icc.1 (hS h2)
  ext x
  simp only [NP, mem_filter, mem_insert, mem_range]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rcases h with (h | h) | (h | h) | ⟨h0, h | h⟩
    · subst h; exact Or.inr (Or.inr ⟨by omega, h1⟩)
    · exact Or.inl h
    · left; rw [show x = t - 1 by omega]; exact h1
    · exact Or.inr (Or.inl h)
    · left; rw [show x = t + 1 by omega]; exact h2
    · exact Or.inr (Or.inr ⟨h0, h⟩)
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rcases h with h | h | ⟨h0, h⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr ⟨h0, Or.inr h⟩)

lemma phi_insert_le {p t : ℕ} (a b : Bool) (z : ℕ → ℕ) {S : Finset ℕ} (h0 : t ∉ S)
    (h1 : t - 1 ∈ S) (h2 : t + 1 ∈ S) (ht : 2 ≤ t) :
    phi p a b z (insert t S) ≤ phi p a b z S := by
  rw [phi, phi, Om_insert a b h1 h2 ht, zs, zs, sum_insert h0]
  push_cast
  linarith [(z t).cast_nonneg (α := ℤ)]

lemma psi_insert_le {p t : ℕ} (z : ℕ → ℕ) {S : Finset ℕ} (hS : S ⊆ Icc 1 p) (h0 : t ∉ S)
    (h1 : t - 1 ∈ S) (h2 : t + 1 ∈ S) (ht : 2 ≤ t) :
    psi p z (insert t S) ≤ psi p z S := by
  rw [psi, psi, NP_insert hS h1 h2 ht, zs, zs, sum_insert h0]
  push_cast
  linarith [(z t).cast_nonneg (α := ℤ)]

lemma zs_union_gap {i j : ℕ} (z : ℕ → ℕ) {B : Finset ℕ} (hgap : ∀ s ∈ B, j + 3 ≤ s) :
    zs z (Ioc i j ∪ B) = zs z (Ioc i j) + zs z B := by
  rw [zs, sum_union]; · rfl
  rw [disjoint_left]
  intro x hx hxB
  have := hgap x hxB
  rw [mem_Ioc] at hx
  omega

lemma Om_union_gap {p i j : ℕ} (a b : Bool) {B : Finset ℕ} (hij : i < j)
    (hB : B ⊆ Icc 1 p) (hBne : B.Nonempty) (hgap : ∀ s ∈ B, j + 3 ≤ s) :
    (Om p a b (Ioc i j ∪ B)).card = (Om p a false (Ioc i j)).card + (Om p false b B).card := by
  have heq : Om p a b (Ioc i j ∪ B) = Om p a false (Ioc i j) ∪ Om p false b B := by
    ext x
    simp only [Om, mem_filter, mem_union, mem_Icc]
    constructor
    · rintro ⟨hx, h⟩
      rcases h with (h | h) | (h | h) | (h | h) | h | h
      · exact Or.inl ⟨hx, Or.inl h⟩
      · exact Or.inr ⟨hx, Or.inl h⟩
      · exact Or.inl ⟨hx, Or.inr (Or.inl h)⟩
      · exact Or.inr ⟨hx, Or.inr (Or.inl h)⟩
      · exact Or.inl ⟨hx, Or.inr (Or.inr (Or.inl h))⟩
      · exact Or.inr ⟨hx, Or.inr (Or.inr (Or.inl h))⟩
      · exact Or.inl ⟨hx, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
      · exact Or.inr ⟨hx, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · refine ⟨hx, ?_⟩
        rcases h with h | h | h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · simp at h
      · refine ⟨hx, ?_⟩
        rcases h with h | h | h | h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
        · simp at h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rw [heq, card_union_of_disjoint]
  rw [disjoint_left]
  intro x hx1 hx2
  obtain ⟨s, hs⟩ := hBne
  have hs1 := hgap s hs
  have hs2 := mem_Icc.1 (hB hs)
  simp only [Om, mem_filter, mem_Icc, mem_Ioc] at hx1 hx2
  obtain ⟨hx, h1⟩ := hx1
  obtain ⟨-, h2⟩ := hx2
  have hle : x ≤ j + 1 := by
    rcases h1 with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · simp at h
  rcases h2 with h | h | h | h | h
  · have := hgap x h; omega
  · have := hgap _ h; omega
  · have := hgap _ h; omega
  · simp at h
  · omega

lemma phi_union_gap {p i j : ℕ} (a b : Bool) (z : ℕ → ℕ) {B : Finset ℕ} (hij : i < j)
    (hB : B ⊆ Icc 1 p) (hBne : B.Nonempty) (hgap : ∀ s ∈ B, j + 3 ≤ s) :
    phi p a b z (Ioc i j ∪ B) = phi p a false z (Ioc i j) + phi p false b z B := by
  rw [phi, phi, phi, Om_union_gap a b hij hB hBne hgap, zs_union_gap z hgap]
  push_cast
  ring

lemma psi_union_gap {p i j : ℕ} (z : ℕ → ℕ) {B : Finset ℕ} (hij : i < j) (hjp : j ≤ p)
    (hgap : ∀ s ∈ B, j + 3 ≤ s) :
    psi p z (Ioc i j ∪ B) = psi p z (Ioc i j) + psi p z B := by
  have heq : NP p (Ioc i j ∪ B) = NP p (Ioc i j) ∪ NP p B := by
    ext x
    simp only [NP, mem_filter, mem_union, mem_range]
    tauto
  rw [psi, psi, psi, heq, card_union_of_disjoint, zs_union_gap z hgap]
  · push_cast; ring
  rw [NP_Ioc_eq hij hjp, disjoint_left]
  intro x hx1 hx2
  simp only [NP, mem_filter, mem_Icc, mem_range] at hx1 hx2
  rcases hx2.2 with h | h | ⟨_, h⟩
  · have := hgap x h; omega
  · have := hgap _ h; omega
  · have := hgap _ h; omega

/-! ## Run induction -/

/-- Number of holes of `S` inside the interval spanned by `S`. -/
def holes (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.max' h + 1 - S.min' h - S.card else 0

lemma card_le_span {S : Finset ℕ} (h : S.Nonempty) : S.card ≤ S.max' h + 1 - S.min' h := by
  have : S ⊆ Icc (S.min' h) (S.max' h) := fun x hx =>
    mem_Icc.2 ⟨S.min'_le x hx, S.le_max' x hx⟩
  simpa using card_le_card this

/-- Run induction: a property of subsets of `{1,…,p}` that holds for `∅` and for intervals,
is inherited from `S ∪ {t}` when `t` fills a gap of size one, and from the pieces when `S`
splits at a gap of size at least two, holds for all subsets. -/
theorem run_induction (p : ℕ) (Q : Finset ℕ → Prop) (h0 : Q ∅)
    (hI : ∀ i j, i < j → j ≤ p → Q (Ioc i j))
    (hfill : ∀ S t, S ⊆ Icc 1 p → t ∉ S → t - 1 ∈ S → t + 1 ∈ S → 2 ≤ t →
      Q (insert t S) → Q S)
    (hsplit : ∀ i j B, i < j → j ≤ p → B ⊆ Icc 1 p → B.Nonempty → (∀ s ∈ B, j + 3 ≤ s) →
      Q B → Q (Ioc i j ∪ B)) :
    ∀ S, S ⊆ Icc 1 p → Q S := by
  intro S
  induction hn : holes S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  intro hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact h0
  set m := S.min' hne with hm
  set M := S.max' hne with hM
  have hmS : m ∈ S := S.min'_mem hne
  have hMS : M ∈ S := S.max'_mem hne
  have hm1 : 1 ≤ m := (mem_Icc.1 (hS hmS)).1
  have hMp : M ≤ p := (mem_Icc.1 (hS hMS)).2
  have hmle : ∀ x ∈ S, m ≤ x := fun x hx => S.min'_le x hx
  have hMge : ∀ x ∈ S, x ≤ M := fun x hx => S.le_max' x hx
  have hex : ∃ t, m ≤ t ∧ t ∈ S ∧ t + 1 ∉ S := ⟨M, hmle M hMS, hMS, fun h => by
    have := hMge _ h; omega⟩
  classical
  let b := Nat.find hex
  have hb : m ≤ b ∧ b ∈ S ∧ b + 1 ∉ S := Nat.find_spec hex
  have hbmin : ∀ t, m ≤ t → t < b → t + 1 ∈ S := by
    intro t ht htb
    by_contra hc
    have hrun : ∀ s, m ≤ s → s ≤ t → s ∈ S := by
      intro s hs1 hs2
      induction s, hs1 using Nat.le_induction with
      | base => exact hmS
      | succ s hs ihs =>
        by_contra hc'
        have := Nat.find_min hex (show s < b by omega)
        exact this ⟨hs, ihs (by omega), hc'⟩
    exact Nat.find_min hex htb ⟨ht, hrun t ht le_rfl, hc⟩
  have hrunb : ∀ s, m ≤ s → s ≤ b → s ∈ S := by
    intro s hs1 hs2
    induction s, hs1 using Nat.le_induction with
    | base => exact hmS
    | succ s hs ihs => exact hbmin s hs (by omega)
  have hbM : b ≤ M := hMge b hb.2.1
  rcases eq_or_lt_of_le hbM with hbM' | hbM'
  · -- `S` is an interval
    have : S = Ioc (m - 1) M := by
      ext x
      simp only [mem_Ioc]
      constructor
      · intro hx; have := hmle x hx; have := hMge x hx; omega
      · intro hx; exact hrunb x (by omega) (by omega)
    rw [this]
    exact hI _ _ (by omega) hMp
  · set B := S.filter (fun x => b < x) with hBdef
    have hBne : B.Nonempty := ⟨M, mem_filter.2 ⟨hMS, hbM'⟩⟩
    set c := B.min' hBne with hc
    have hcB : c ∈ B := B.min'_mem hBne
    have hcS : c ∈ S := (mem_filter.1 hcB).1
    have hbc : b < c := (mem_filter.1 hcB).2
    have hcle : ∀ x ∈ B, c ≤ x := fun x hx => B.min'_le x hx
    have hc2 : b + 2 ≤ c := by
      rcases eq_or_lt_of_le (show b + 1 ≤ c by omega) with h | h
      · exact absurd (h ▸ hcS) hb.2.2
      · omega
    have hSeq : S = Ioc (m - 1) b ∪ B := by
      ext x
      simp only [mem_union, mem_Ioc, hBdef, mem_filter]
      constructor
      · intro hx
        by_cases hxb : b < x
        · exact Or.inr ⟨hx, hxb⟩
        · exact Or.inl ⟨by have := hmle x hx; omega, by omega⟩
      · rintro (hx | hx)
        · exact hrunb x (by omega) hx.2
        · exact hx.1
    have hholesS : holes S = M + 1 - m - S.card := by simp [holes, hne, hm, hM]
    rcases eq_or_lt_of_le hc2 with hc2' | hc2'
    · -- fill the gap `b + 1`
      have hb1 : b + 1 ∉ S := hb.2.2
      apply hfill S (b + 1) hS hb1 (by simpa using hb.2.1) (by rw [show b + 1 + 1 = c by omega]; exact hcS) (by omega)
      have hS' : insert (b + 1) S ⊆ Icc 1 p := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_Icc.2 ⟨by omega, by omega⟩
        · exact hS hx
      have hne' : (insert (b + 1) S).Nonempty := insert_nonempty _ _
      have hmin' : (insert (b + 1) S).min' hne' = m := by
        apply le_antisymm
        · exact min'_le _ _ (mem_insert_of_mem hmS)
        · apply le_min'
          intro y hy
          rcases mem_insert.1 hy with rfl | hy
          · omega
          · exact hmle y hy
      have hmax' : (insert (b + 1) S).max' hne' = M := by
        apply le_antisymm
        · apply max'_le
          intro y hy
          rcases mem_insert.1 hy with rfl | hy
          · omega
          · exact hMge y hy
        · exact le_max' _ _ (mem_insert_of_mem hMS)
      have hcard := card_le_span hne'
      rw [hmin', hmax', card_insert_of_notMem hb1] at hcard
      refine ih (holes (insert (b + 1) S)) ?_ _ rfl hS'
      rw [← hn, hholesS]
      simp only [holes, hne', dite_true, hmin', hmax', card_insert_of_notMem hb1]
      omega
    · -- split at the gap `b+1, …, c-1`
      rw [hSeq]
      have hBsub : B ⊆ Icc 1 p := fun x hx => hS (mem_filter.1 hx).1
      have hgap : ∀ s ∈ B, b + 3 ≤ s := fun s hs => by have := hcle s hs; omega
      apply hsplit (m - 1) b B (by omega) (by omega) hBsub hBne hgap
      refine ih (holes B) ?_ B rfl hBsub
      have hminB : B.min' hBne = c := rfl
      have hmaxB : B.max' hBne = M := by
        apply le_antisymm
        · exact max'_le _ _ _ (fun y hy => hMge y (mem_filter.1 hy).1)
        · exact le_max' _ _ (mem_filter.2 ⟨hMS, hbM'⟩)
      have hcardS : S.card = (Ioc (m - 1) b).card + B.card := by
        conv_lhs => rw [hSeq]
        rw [card_union_of_disjoint]
        rw [disjoint_left]
        intro x hx hxB
        have := (mem_filter.1 hxB).2
        rw [mem_Ioc] at hx
        omega
      have hcB' := card_le_span hBne
      rw [hminB, hmaxB] at hcB'
      rw [Nat.card_Ioc] at hcardS
      have hcS' := card_le_span hne
      rw [← hn, hholesS]
      simp only [holes, hBne, dite_true, hminB, hmaxB]
      rw [← hm, ← hM] at hcS'
      omega

end Ear
```

### `PathBounds.lean`

```lean
import PathRuns

/-!
# Explicit c-values of the ear (Lemma 2.1 of the proof, made explicit)

`Rc`: every rise of the prefix-sum walk is at most `1` (this is condition (P) of the proof);
`Fc`: every fall is at most `2`.  Under these hypotheses we compute lower bounds of
`φ_σ(S)` valid for *all* `S ⊆ {1,…,p}` by run induction, and exhibit the sets attaining them.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Ear

/-- All rises of the walk are at most one. -/
def Rc (p : ℕ) (z : ℕ → ℕ) : Prop := ∀ i j, i < j → j ≤ p → P z j - P z i ≤ 1
/-- All falls of the walk are at most two. -/
def Fc (p : ℕ) (z : ℕ → ℕ) : Prop := ∀ i j, i < j → j ≤ p → P z i - P z j ≤ 2

open scoped Classical in
/-- Explicit value of `c_u` (non-tight case). -/
noncomputable def C10 (p : ℕ) (z : ℕ → ℕ) : ℤ :=
  if P z p ≤ -1 ∧ ∀ j ∈ range (p + 1), P z j ≤ 0 then 1 else 0
open scoped Classical in
/-- Explicit value of `c_v` (non-tight case). -/
noncomputable def C01 (p : ℕ) (z : ℕ → ℕ) : ℤ :=
  if P z p ≤ -1 ∧ ∀ j ∈ range (p + 1), P z p ≤ P z j then 1 else 0

variable {p : ℕ} {z : ℕ → ℕ}

lemma C10_nonneg : 0 ≤ C10 p z := by unfold C10; split_ifs <;> norm_num
lemma C01_nonneg : 0 ≤ C01 p z := by unfold C01; split_ifs <;> norm_num
lemma C10_le_one : C10 p z ≤ 1 := by unfold C10; split_ifs <;> norm_num
lemma C01_le_one : C01 p z ≤ 1 := by unfold C01; split_ifs <;> norm_num

/-! ## Interval cases -/

lemma phi00_Ioc_nonneg (hR : Rc p z) (hT : P z p ≤ 0) {i j : ℕ} (hij : i < j) (hjp : j ≤ p) :
    0 ≤ phi p false false z (Ioc i j) := by
  rw [phi_Ioc false false z hij hjp]
  have h1 := hR i j hij hjp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases eq_or_lt_of_le hjp with rfl | hj
    · simp; omega
    · simp [hj] at h1 ⊢; omega
  · simp [show 1 ≤ i by omega]
    split_ifs <;> omega

lemma phi10_Ioc (hR : Rc p z) (hT : P z p ≤ 0) {i j : ℕ} (hij : i < j) (hjp : j ≤ p) :
    C10 p z ≤ phi p true false z (Ioc i j) := by
  have h1 := hR i j hij hjp
  have hlb := P_lb z (show i ≤ j from hij.le)
  unfold C10
  split_ifs with hC
  · obtain ⟨hTn, hall⟩ := hC
    have hPj := hall j (mem_range.2 (by omega))
    have hPi := hall i (mem_range.2 (by omega))
    rw [phi_Ioc true false z hij hjp]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases eq_or_lt_of_le hjp with rfl | hj
      · simp; omega
      · simp [hj]; omega
    · rcases (show 1 ≤ i by omega).eq_or_lt with rfl | hi2
      · have h01 := P_lb z (show 0 ≤ 1 from zero_le_one)
        simp at h01
        rcases eq_or_lt_of_le hjp with rfl | hj
        · simp; omega
        · simp [hj]; omega
      · simp [show 1 ≤ i by omega, show 2 ≤ i by omega]
        split_ifs <;> omega
  · rw [phi_Ioc true false z hij hjp]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases eq_or_lt_of_le hjp with rfl | hj
      · simp; omega
      · simp [hj] at h1 ⊢; omega
    · simp [show 1 ≤ i by omega]
      split_ifs <;> omega

lemma phi01_Ioc (hR : Rc p z) (hT : P z p ≤ 0) {i j : ℕ} (hij : i < j) (hjp : j ≤ p) :
    C01 p z ≤ phi p false true z (Ioc i j) := by
  have h1 := hR i j hij hjp
  have hlbjp := P_lb z hjp
  unfold C01
  split_ifs with hC
  · obtain ⟨hTn, hall⟩ := hC
    have hPi := hall i (mem_range.2 (by omega))
    rw [phi_Ioc false true z hij hjp]
    rcases eq_or_lt_of_le hjp with rfl | hj
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp; omega
      · simp [show 1 ≤ i by omega]; omega
    · rcases Nat.lt_or_ge (j + 2) (p + 1) with hj2 | hj2
      · simp [hj, show j + 2 ≤ p by omega]
        split_ifs <;> omega
      · have hjp1 : p = j + 1 := by omega
        subst hjp1
        simp at hlbjp
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · simp at hPi ⊢; omega
        · simp [show 1 ≤ i by omega]; omega
  · rw [phi_Ioc false true z hij hjp]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases eq_or_lt_of_le hjp with rfl | hj
      · simp; omega
      · simp [hj] at h1 ⊢; split_ifs <;> omega
    · simp [show 1 ≤ i by omega]
      split_ifs <;> omega

lemma phi11_Ioc (hR : Rc p z) (hF : Fc p z) (hT : P z p ≤ 0) {i j : ℕ} (hij : i < j)
    (hjp : j ≤ p) : -P z p ≤ phi p true true z (Ioc i j) := by
  rw [phi_Ioc true true z hij hjp]
  have h1 := hR i j hij hjp
  have hlbjp := P_lb z hjp
  have hlb0i := P_lb z (Nat.zero_le i)
  simp only [P_zero, zero_sub] at hlb0i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases eq_or_lt_of_le hjp with rfl | hj
    · simp
    · have hFj := hF j p hj le_rfl
      simp [hj]
      split_ifs with h2
      · omega
      · have : p = j + 1 := by omega
        subst this; simp at hlbjp; omega
  · have hF0i := hF 0 i hi (by omega)
    simp only [P_zero] at hF0i
    rcases eq_or_lt_of_le hjp with rfl | hj
    · simp [show 1 ≤ i by omega]
      split_ifs with h2
      · omega
      · have : i = 1 := by omega
        subst this; omega
    · have hFj := hF j p hj le_rfl
      simp [show 1 ≤ i by omega, hj]
      split_ifs with h2 h3 h3
      · omega
      · have : p = j + 1 := by omega
        subst this; simp at hlbjp; omega
      · have : i = 1 := by omega
        subst this; omega
      · have : p = j + 1 := by omega
        subst this
        have : i = 1 := by omega
        subst this; simp at hlbjp; omega

lemma psi_Ioc_pos (hR : Rc p z) {i j : ℕ} (hij : i < j) (hjp : j ≤ p) :
    1 ≤ psi p z (Ioc i j) := by
  rw [psi_Ioc z hij hjp]; have := hR i j hij hjp; omega

/-! ## Empty set -/

lemma card_Om_empty (a b : Bool) (hp : 1 ≤ p) :
    ((Om p a b ∅).card : ℤ) = (if a = true then 1 else 0)
      + (if b = true ∧ (a = false ∨ 2 ≤ p) then 1 else 0) := by
  have : Om p a b ∅ = (if a = true then {1} else ∅) ∪
      (if b = true ∧ (a = false ∨ 2 ≤ p) then {p} else ∅) := by
    ext t
    simp only [Om, mem_filter, mem_Icc, notMem_empty, false_or, mem_union]
    cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte,
      true_or, false_or, Bool.true_eq_false, eq_self_iff_true] <;> (try split_ifs) <;> (try simp) <;> omega
  rw [this, card_union_of_disjoint]
  · cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte,
      true_or, false_or, Bool.true_eq_false, eq_self_iff_true] <;> (try split_ifs) <;> simp
  · cases a <;> cases b <;> simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte,
      true_or, false_or, Bool.true_eq_false, eq_self_iff_true] <;> (try split_ifs) <;> simp <;> omega

/-! ## Run induction for the lower bounds -/

/-- Lower bounds for the types `(0,0)`, `(1,0)`, `(0,1)`. -/
theorem lb_main (hR : Rc p z) (hT : P z p ≤ 0) (hp : 1 ≤ p) :
    ∀ S ⊆ Icc 1 p, 0 ≤ phi p false false z S ∧ C10 p z ≤ phi p true false z S ∧
      C01 p z ≤ phi p false true z S := by
  apply run_induction p
  · refine ⟨?_, ?_, ?_⟩
    · rw [phi_empty, card_Om_empty _ _ hp]; simp
    · rw [phi_empty, card_Om_empty _ _ hp]; simp; exact C10_le_one
    · rw [phi_empty, card_Om_empty _ _ hp]; simp; exact C01_le_one
  · intro i j hij hjp
    exact ⟨phi00_Ioc_nonneg hR hT hij hjp, phi10_Ioc hR hT hij hjp, phi01_Ioc hR hT hij hjp⟩
  · intro S t hS h0 h1 h2 ht ⟨q1, q2, q3⟩
    exact ⟨q1.trans (phi_insert_le _ _ z h0 h1 h2 ht), q2.trans (phi_insert_le _ _ z h0 h1 h2 ht),
      q3.trans (phi_insert_le _ _ z h0 h1 h2 ht)⟩
  · intro i j B hij hjp hB hBne hgap ⟨q1, q2, q3⟩
    rw [phi_union_gap _ _ z hij hB hBne hgap, phi_union_gap _ _ z hij hB hBne hgap,
      phi_union_gap _ _ z hij hB hBne hgap]
    have a1 := phi00_Ioc_nonneg hR hT hij hjp
    have a2 := phi10_Ioc hR hT hij hjp
    exact ⟨by linarith, by linarith, by linarith⟩

lemma Csum (hR : Rc p z) (hF : Fc p z) (hT : P z p ≤ 0) : -P z p ≤ C10 p z + C01 p z := by
  have hF0p := fun (h : 0 < p) => hF 0 p h le_rfl
  unfold C10 C01
  split_ifs with h1 h2 h2
  · rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at h1
    · have := hF0p hp; simp at this; omega
  · -- c_u = 1, c_v = 0
    push Not at h2
    obtain ⟨j, hj, hPj⟩ := h2 h1.1
    rw [mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp at hPj; omega
    · have := hF 0 j hjpos (by omega); simp at this; omega
  · push Not at h1
    obtain ⟨j, hj, hPj⟩ := h1 h2.1
    rw [mem_range] at hj
    rcases eq_or_lt_of_le (show j ≤ p by omega) with rfl | hjp
    · omega
    · have := hF j p hjp le_rfl; omega
  · by_contra hc
    push Not at h1 h2
    obtain ⟨i, hi, hPi⟩ := h1 (by omega)
    obtain ⟨j, hj, hPj⟩ := h2 (by omega)
    rw [mem_range] at hi hj
    rcases lt_trichotomy i j with hij | rfl | hij
    · have := hF i j hij (by omega); omega
    · omega
    · have := hR j i hij (by omega); omega

/-- Lower bound for the type `(1,1)`. -/
theorem lb11 (hR : Rc p z) (hF : Fc p z) (hT : P z p ≤ 0) (hp : 1 ≤ p) :
    ∀ S ⊆ Icc 1 p, -P z p ≤ phi p true true z S := by
  apply run_induction p
  · rw [phi_empty, card_Om_empty _ _ hp]
    have h0p := hF 0 p hp le_rfl
    have hl := P_lb z (show 0 ≤ p from Nat.zero_le p)
    simp at h0p hl ⊢
    split_ifs with h2
    · omega
    · have : p = 1 := by omega
      subst this; simp at hl; omega
  · intro i j hij hjp; exact phi11_Ioc hR hF hT hij hjp
  · intro S t hS h0 h1 h2 ht q; exact q.trans (phi_insert_le _ _ z h0 h1 h2 ht)
  · intro i j B hij hjp hB hBne hgap q
    rw [phi_union_gap _ _ z hij hB hBne hgap]
    have a1 := phi10_Ioc hR hT hij hjp
    have a2 := (lb_main hR hT hp B hB).2.2
    have := Csum hR hF hT
    linarith

/-- Validity: `z(S) < |N_P[S]|` for all nonempty `S`. -/
theorem lb_psi (hR : Rc p z) : ∀ S ⊆ Icc 1 p, S.Nonempty → 1 ≤ psi p z S := by
  intro S hS
  revert S
  refine run_induction p (fun S => S.Nonempty → 1 ≤ psi p z S) ?_ ?_ ?_ ?_
  · intro h; simp at h
  · intro i j hij hjp _; exact psi_Ioc_pos hR hij hjp
  · intro S t hS h0 h1 h2 ht q _
    exact (q (insert_nonempty _ _)).trans (psi_insert_le z hS h0 h1 h2 ht)
  · intro i j B hij hjp hB hBne hgap q _
    rw [psi_union_gap z hij hjp hgap]
    have := psi_Ioc_pos hR hij hjp
    have := q hBne
    linarith

/-! ## Witnesses -/

lemma phi_W (a b : Bool) (hp : 1 ≤ p) : phi p a b z (Ioc 0 p) = -P z p := by
  rw [phi_Ioc a b z hp le_rfl]; simp

/-- `c_u ≤ C10`: some set attains at most the explicit value. -/
lemma wit10 (hT : P z p ≤ 0) (hp : 1 ≤ p) :
    ∃ S ⊆ Icc 1 p, phi p true false z S ≤ C10 p z := by
  unfold C10
  split_ifs with h
  · refine ⟨∅, empty_subset _, ?_⟩
    rw [phi_empty, card_Om_empty _ _ hp]; simp
  · push Not at h
    by_cases hT0 : P z p = 0
    · exact ⟨Ioc 0 p, fun x hx => by simp at hx ⊢; omega, by rw [phi_W _ _ hp]; omega⟩
    · obtain ⟨j, hj, hPj⟩ := h (by omega)
      rw [mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp at hPj
      rcases eq_or_lt_of_le (show j ≤ p by omega) with rfl | hjp
      · omega
      refine ⟨Ioc 0 j, fun x hx => by simp at hx ⊢; omega, ?_⟩
      rw [phi_Ioc true false z hj0 hjp.le]
      simp [hjp]; omega

lemma wit01 (hT : P z p ≤ 0) (hp : 1 ≤ p) :
    ∃ S ⊆ Icc 1 p, phi p false true z S ≤ C01 p z := by
  unfold C01
  split_ifs with h
  · refine ⟨∅, empty_subset _, ?_⟩
    rw [phi_empty, card_Om_empty _ _ hp]; simp
  · push Not at h
    by_cases hT0 : P z p = 0
    · exact ⟨Ioc 0 p, fun x hx => by simp at hx ⊢; omega, by rw [phi_W _ _ hp]; omega⟩
    · obtain ⟨j, hj, hPj⟩ := h (by omega)
      rw [mem_range] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp at hPj; omega
      rcases eq_or_lt_of_le (show j ≤ p by omega) with rfl | hjp
      · omega
      refine ⟨Ioc j p, fun x hx => by simp at hx ⊢; omega, ?_⟩
      rw [phi_Ioc false true z hjp le_rfl]
      simp [show 1 ≤ j by omega]; omega

/-- A fall of three or more is detected by some set with `φ₁₁ < -T`. -/
lemma wit_fall (hp : 1 ≤ p) {i j : ℕ} (hij : i < j) (hjp : j ≤ p) (hfall : 3 ≤ P z i - P z j) :
    ∃ S ⊆ Icc 1 p, phi p true true z S ≤ -P z p - 1 := by
  have hlbij := P_lb z hij.le
  have hgap : i + 3 ≤ j := by omega
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases eq_or_lt_of_le hjp with rfl | hj
    · refine ⟨∅, empty_subset _, ?_⟩
      rw [phi_empty, card_Om_empty _ _ hp]; simp at hfall ⊢; split_ifs <;> omega
    · refine ⟨Ioc j p, fun x hx => by simp at hx ⊢; omega, ?_⟩
      rw [phi_Ioc true true z hj le_rfl]
      simp [show 1 ≤ j by omega, show 2 ≤ j by omega] at hfall ⊢; omega
  · rcases eq_or_lt_of_le hjp with rfl | hj
    · refine ⟨Ioc 0 i, fun x hx => by simp at hx ⊢; omega, ?_⟩
      rw [phi_Ioc true true z hi (by omega)]
      simp [show i < j by omega, show i + 2 ≤ j by omega]; omega
    · refine ⟨Ioc 0 i ∪ Ioc j p, ?_, ?_⟩
      · intro x hx; simp at hx ⊢; omega
      · have hB : Ioc j p ⊆ Icc 1 p := fun x hx => by simp at hx ⊢; omega
        have hBne : (Ioc j p).Nonempty := ⟨p, by simp; omega⟩
        rw [phi_union_gap true true z hi hB hBne (fun s hs => by simp at hs; omega),
          phi_Ioc true false z hi (by omega), phi_Ioc false true z hj le_rfl]
        simp [show i < p by omega, show 1 ≤ j by omega]; omega

end Ear
```

### `Drac.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith

/-!
# Draconian sequences (Davis–Chen, Definition 1 rephrased)

For a simple graph `G` on a finite vertex set `V` with `N = |V|`, a sequence `x : V → ℕ`
is *D(G)-draconian* if `∑ x = N - 1` and for every nonempty `S ⊆ V`,
`∑_{i ∈ S} x i < |S ∪ ⋃_{i ∈ S} N_G(i)|`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closed neighbourhood `S ∪ ⋃_{i ∈ S} N_G(i)` (in the source: `⋃_j N_{D(G)}(i_j)`). -/
def cnbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ univ.filter (fun j => ∃ i ∈ S, G.Adj i j)

/-- The draconian inequalities and the sum condition. -/
def IsDraconian (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℕ) : Prop :=
  ∑ i, x i = Fintype.card V - 1 ∧
    ∀ S : Finset V, S.Nonempty → ∑ i ∈ S, x i < (cnbhd G S).card

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (IsDraconian G) := by
  intro x; unfold IsDraconian; infer_instance

/-- The finite set `D(G)` of D(G)-draconian sequences.  (The bound `x i < N` is automatic
from `∑ x = N - 1`; it only makes the set a `Finset`, see `mem_draconian`.) -/
def draconian (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V → ℕ) :=
  (Fintype.piFinset fun _ => range (Fintype.card V)).filter (IsDraconian G)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma mem_draconian {x : V → ℕ} : x ∈ draconian G ↔ IsDraconian G x := by
  unfold draconian
  rw [mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    rw [mem_range]
    have hi : x i ≤ ∑ j, x j := single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨i⟩
    rw [h.1] at hi
    omega

lemma mem_cnbhd {S : Finset V} {j : V} : j ∈ cnbhd G S ↔ j ∈ S ∨ ∃ i ∈ S, G.Adj i j := by
  simp [cnbhd]

lemma subset_cnbhd (S : Finset V) : S ⊆ cnbhd G S := subset_union_left

lemma cnbhd_mono {S T : Finset V} (h : S ⊆ T) : cnbhd G S ⊆ cnbhd G T := by
  intro j hj
  rw [mem_cnbhd] at hj ⊢
  rcases hj with hj | ⟨i, hi, hij⟩
  · exact Or.inl (h hj)
  · exact Or.inr ⟨i, h hi, hij⟩

lemma cnbhd_union (S T : Finset V) : cnbhd G (S ∪ T) = cnbhd G S ∪ cnbhd G T := by
  ext j
  simp only [mem_union, mem_cnbhd]
  constructor
  · rintro ((h | h) | ⟨i, hi | hi, hij⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨i, hi, hij⟩)
    · exact Or.inr (Or.inr ⟨i, hi, hij⟩)
  · rintro ((h | ⟨i, hi, hij⟩) | (h | ⟨i, hi, hij⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨i, Or.inl hi, hij⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨i, Or.inr hi, hij⟩

lemma cnbhd_inter_subset (S T : Finset V) : cnbhd G (S ∩ T) ⊆ cnbhd G S ∩ cnbhd G T :=
  subset_inter (cnbhd_mono inter_subset_left) (cnbhd_mono inter_subset_right)

/-- Submodularity of the closed-neighbourhood size. -/
lemma card_cnbhd_submod (S T : Finset V) :
    (cnbhd G (S ∪ T)).card + (cnbhd G (S ∩ T)).card ≤ (cnbhd G S).card + (cnbhd G T).card := by
  rw [cnbhd_union]
  have h1 := card_union_add_card_inter (cnbhd G S) (cnbhd G T)
  have h2 := card_le_card (cnbhd_inter_subset (G := G) S T)
  omega

lemma card_cnbhd_le (S : Finset V) : (cnbhd G S).card ≤ Fintype.card V :=
  card_le_univ _

lemma card_cnbhd_pos {S : Finset V} (h : S.Nonempty) : 1 ≤ (cnbhd G S).card :=
  card_pos.2 (h.mono (subset_cnbhd S))

/-! ## Invariance under graph isomorphism -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `|D(G)|` is invariant under relabelling the vertices. -/
theorem card_draconian_congr (G' : SimpleGraph W) [DecidableRel G'.Adj] (e : V ≃ W)
    (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b) :
    (draconian G).card = (draconian G').card := by
  have hN : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hcn : ∀ S : Finset V, (cnbhd G' (S.map e.toEmbedding)).card = (cnbhd G S).card := by
    intro S
    have : cnbhd G' (S.map e.toEmbedding) = (cnbhd G S).map e.toEmbedding := by
      ext w
      obtain ⟨a, rfl⟩ := e.surjective w
      simp only [mem_cnbhd, mem_map_equiv, Equiv.symm_apply_apply, mem_map]
      constructor
      · rintro (h | ⟨i, hi, hij⟩)
        · exact ⟨a, Or.inl (by simpa using h), rfl⟩
        · obtain ⟨b, hb, rfl⟩ := hi
          exact ⟨a, Or.inr ⟨b, hb, (he b a).1 hij⟩, rfl⟩
      · rintro ⟨c, hc, hca⟩
        have := e.injective hca
        subst this
        rcases hc with h | ⟨i, hi, hij⟩
        · exact Or.inl ⟨c, h, rfl⟩
        · exact Or.inr ⟨e i, ⟨i, hi, rfl⟩, (he i c).2 hij⟩
    rw [this, card_map]
  apply card_bij (fun x _ => x ∘ e.symm)
  · intro x hx
    rw [mem_draconian] at hx ⊢
    obtain ⟨hs, hS⟩ := hx
    refine ⟨?_, fun S' hS' => ?_⟩
    · rw [← hN, ← hs]
      exact Equiv.sum_comp e.symm x
    · set S := S'.map e.symm.toEmbedding
      have hS'eq : S' = S.map e.toEmbedding := by
        ext w; simp [S]
      have h1 := hS S (by simpa [S] using hS')
      rw [hS'eq, hcn]
      simpa [S, sum_map] using h1
  · intro x _ y _ hxy
    funext a
    have := congrFun hxy (e a)
    simpa using this
  · intro x' hx'
    refine ⟨x' ∘ e, ?_, by funext w; simp⟩
    rw [mem_draconian] at hx' ⊢
    obtain ⟨hs, hS⟩ := hx'
    refine ⟨?_, fun S hS0 => ?_⟩
    · rw [hN, ← hs]
      exact Equiv.sum_comp e x'
    · have h1 := hS (S.map e.toEmbedding) (by simpa using hS0)
      rw [hcn] at h1
      simpa [sum_map] using h1

end Drac
```

### `FibreCount.lean`

```lean
import Drac
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-!
# Fibres of `D(G)` in the direction `e_u - e_v`

For two distinct vertices `u, v`, the fibre of `D(G)` over a fixed value of all other
coordinates is an integer interval of values of `x_u`.  Consequently
* `|D(G) + {a e_u + (k-a) e_v : lo ≤ a ≤ hi}| = |D(G)| + (hi - lo) · #fib`,
* `|{y : y + e_u ∈ D(G), y + e_v ∈ D(G)}| = |D(G)| - #fib`,
where `#fib` is the number of nonempty fibres (Lemmas 2.2 and 2.3 of the proof, counting part).
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `a` at vertex `u`, zero elsewhere. -/
def ind (u : V) (a : ℕ) : V → ℕ := fun w => if w = u then a else 0

/-- Forget the coordinates at `u` and `v`. -/
def proj (u v : V) (y : V → ℕ) : V → ℕ := fun w => if w = u ∨ w = v then 0 else y w

lemma sum_ind (u : V) (a : ℕ) (S : Finset V) : ∑ w ∈ S, ind u a w = if u ∈ S then a else 0 := by
  simp only [ind]; exact sum_ite_eq' S u (fun _ => a)

lemma sum_eq_proj (u v : V) (huv : u ≠ v) (y : V → ℕ) (S : Finset V) :
    ∑ w ∈ S, y w = ∑ w ∈ S, proj u v y w + (if u ∈ S then y u else 0)
      + (if v ∈ S then y v else 0) := by
  have : ∀ w, y w = proj u v y w + ind u (y u) w + ind v (y v) w := by
    intro w
    simp only [proj, ind]
    by_cases h1 : w = u
    · subst h1; simp [huv]
    · by_cases h2 : w = v
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [sum_congr rfl (fun w _ => this w), sum_add_distrib, sum_add_distrib, sum_ind, sum_ind]

lemma proj_add_ind_u (u v : V) (y : V → ℕ) (a : ℕ) : proj u v (y + ind u a) = proj u v y := by
  funext w; simp only [proj, ind, Pi.add_apply]; split_ifs <;> simp_all

lemma proj_add_ind_v (u v : V) (y : V → ℕ) (a : ℕ) : proj u v (y + ind v a) = proj u v y := by
  funext w; simp only [proj, ind, Pi.add_apply]; split_ifs <;> simp_all

lemma eq_of_proj (u v : V) (huv : u ≠ v) {y₁ y₂ : V → ℕ} (hs : ∑ w, y₁ w = ∑ w, y₂ w)
    (hp : proj u v y₁ = proj u v y₂) (hu : y₁ u = y₂ u) : y₁ = y₂ := by
  have h1 := sum_eq_proj u v huv y₁ univ
  have h2 := sum_eq_proj u v huv y₂ univ
  simp only [mem_univ, ite_true] at h1 h2
  rw [hp] at h1
  have hv : y₁ v = y₂ v := by omega
  funext w
  by_cases hwu : w = u
  · subst hwu; exact hu
  by_cases hwv : w = v
  · subst hwv; exact hv
  have := congrFun hp w
  simpa [proj, hwu, hwv] using this

/-- The set of values `y u` over `y ∈ Y` with `proj y = w`. -/
def uvals (u v : V) (Y : Finset (V → ℕ)) (w : V → ℕ) : Finset ℕ :=
  (Y.filter (fun y => proj u v y = w)).image (fun y => y u)

lemma card_eq_sum_uvals (u v : V) (huv : u ≠ v) (Y : Finset (V → ℕ)) (s : ℕ)
    (hY : ∀ y ∈ Y, ∑ w, y w = s) (W0 : Finset (V → ℕ)) (hW0 : ∀ y ∈ Y, proj u v y ∈ W0) :
    Y.card = ∑ w ∈ W0, (uvals u v Y w).card := by
  rw [card_eq_sum_card_fiberwise hW0]
  refine sum_congr rfl (fun w _ => ?_)
  rw [uvals, card_image_of_injOn]
  intro y₁ hy₁ y₂ hy₂ h
  simp only [coe_filter] at hy₁ hy₂
  exact eq_of_proj u v huv ((hY _ hy₁.1).trans (hY _ hy₂.1).symm) (hy₁.2.trans hy₂.2.symm) h

lemma mem_uvals {u v : V} {Y : Finset (V → ℕ)} {w : V → ℕ} {c : ℕ} :
    c ∈ uvals u v Y w ↔ ∃ y ∈ Y, proj u v y = w ∧ y u = c := by
  simp [uvals, and_assoc]

/-- Convexity of the fibres of `D(G)`. -/
lemma uvals_convex (u v : V) (huv : u ≠ v) {w : V → ℕ} {a b c : ℕ}
    (ha : a ∈ uvals u v (draconian G) w) (hb : b ∈ uvals u v (draconian G) w)
    (hac : a ≤ c) (hcb : c ≤ b) : c ∈ uvals u v (draconian G) w := by
  rw [mem_uvals] at ha hb ⊢
  obtain ⟨x₁, hx₁, hp₁, rfl⟩ := ha
  obtain ⟨x₃, hx₃, hp₃, rfl⟩ := hb
  rw [mem_draconian] at hx₁ hx₃
  set s := x₁ u + x₁ v with hs
  have hsum1 := sum_eq_proj u v huv x₁ univ
  have hsum3 := sum_eq_proj u v huv x₃ univ
  simp only [mem_univ, ite_true] at hsum1 hsum3
  rw [hp₃.trans hp₁.symm] at hsum3
  have e1 := hx₁.1
  have e3 := hx₃.1
  have h31 : x₃ u + x₃ v = s := by rw [hs]; omega
  set x₂ : V → ℕ := fun w' => if w' = u then c else if w' = v then s - c else x₁ w' with hx₂
  have hpr : proj u v x₂ = proj u v x₁ := by
    funext w'; simp only [proj, hx₂]; split_ifs <;> simp_all
  refine ⟨x₂, ?_, hpr.trans hp₁, by simp [hx₂]⟩
  rw [mem_draconian]
  have hx2u : x₂ u = c := by simp [hx₂]
  have hx2v : x₂ v = s - c := by simp [hx₂, huv.symm]
  refine ⟨?_, fun S hS => ?_⟩
  · have := sum_eq_proj u v huv x₂ univ
    simp only [mem_univ, ite_true] at this
    rw [hpr, hx2u, hx2v] at this
    have hcs : c ≤ s := by omega
    rw [this, ← hx₁.1, hsum1]
    omega
  · have e2 := sum_eq_proj u v huv x₂ S
    have e1 := sum_eq_proj u v huv x₁ S
    have e3 := sum_eq_proj u v huv x₃ S
    rw [hpr] at e2
    rw [hp₃.trans hp₁.symm] at e3
    have b1 := hx₁.2 S hS
    have b3 := hx₃.2 S hS
    rw [hx2u, hx2v] at e2
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp only [hu, hv, ite_true, ite_false] at e1 e2 e3 <;> omega

/-- A convex nonempty finite set of naturals is an interval. -/
lemma eq_Icc_of_convex {A : Finset ℕ} (hne : A.Nonempty)
    (hconv : ∀ a ∈ A, ∀ b ∈ A, ∀ c, a ≤ c → c ≤ b → c ∈ A) :
    A = Icc (A.min' hne) (A.max' hne) := by
  ext c
  rw [mem_Icc]
  constructor
  · intro hc; exact ⟨A.min'_le c hc, A.le_max' c hc⟩
  · rintro ⟨h1, h2⟩; exact hconv _ (A.min'_mem hne) _ (A.max'_mem hne) c h1 h2

lemma uvals_D_Icc (u v : V) (huv : u ≠ v) {w : V → ℕ}
    (hw : w ∈ (draconian G).image (proj u v)) :
    ∃ q₀ q₁, q₀ ≤ q₁ ∧ uvals u v (draconian G) w = Icc q₀ q₁ := by
  have hne : (uvals u v (draconian G) w).Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hw
    exact ⟨x u, mem_uvals.2 ⟨x, hx, rfl, rfl⟩⟩
  refine ⟨_, _, min'_le_max' _ hne, eq_Icc_of_convex hne ?_⟩
  intro a ha b hb c h1 h2
  exact uvals_convex u v huv ha hb h1 h2

/-! ## Minkowski sum with a segment -/

/-- `D(G) + {a e_u + (k-a) e_v : lo ≤ a ≤ hi}`. -/
def mink (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (k lo hi : ℕ) : Finset (V → ℕ) :=
  ((draconian G) ×ˢ Icc lo hi).image (fun q => q.1 + ind u q.2 + ind v (k - q.2))

lemma mem_mink {u v : V} {k lo hi : ℕ} {y : V → ℕ} :
    y ∈ mink G u v k lo hi ↔
      ∃ x ∈ draconian G, ∃ a, lo ≤ a ∧ a ≤ hi ∧ y = x + ind u a + ind v (k - a) := by
  simp only [mink, mem_image, mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨x, a, ⟨hx, ha1, ha2⟩, rfl⟩; exact ⟨x, hx, a, ha1, ha2, rfl⟩
  · rintro ⟨x, hx, a, ha1, ha2, rfl⟩; exact ⟨x, a, ⟨hx, ha1, ha2⟩, rfl⟩

theorem card_mink (u v : V) (huv : u ≠ v) {k lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ k) :
    (mink G u v k lo hi).card =
      (draconian G).card + (hi - lo) * ((draconian G).image (proj u v)).card := by
  set W0 := (draconian G).image (proj u v)
  have hsumD : ∀ x ∈ draconian G, ∑ w, x w = Fintype.card V - 1 :=
    fun x hx => (mem_draconian.1 hx).1
  have hD := card_eq_sum_uvals u v huv (draconian G) _ hsumD W0
    (fun y hy => mem_image_of_mem _ hy)
  have hM := card_eq_sum_uvals u v huv (mink G u v k lo hi) (Fintype.card V - 1 + k)
    (by
      intro y hy
      obtain ⟨x, hx, a, ha1, ha2, rfl⟩ := mem_mink.1 hy
      simp only [Pi.add_apply, sum_add_distrib, sum_ind, mem_univ, ite_true, hsumD x hx]
      omega)
    W0 (by
      intro y hy
      obtain ⟨x, hx, a, ha1, ha2, rfl⟩ := mem_mink.1 hy
      rw [proj_add_ind_v, proj_add_ind_u]
      exact mem_image_of_mem _ hx)
  rw [hM, hD, mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
  refine sum_congr rfl (fun w hw => ?_)
  obtain ⟨q₀, q₁, hq, hI⟩ := uvals_D_Icc u v huv hw
  have : uvals u v (mink G u v k lo hi) w = Icc (q₀ + lo) (q₁ + hi) := by
    ext c
    rw [mem_uvals, mem_Icc]
    constructor
    · rintro ⟨y, hy, hpy, rfl⟩
      obtain ⟨x, hx, a, ha1, ha2, rfl⟩ := mem_mink.1 hy
      rw [proj_add_ind_v, proj_add_ind_u] at hpy
      have hxu : x u ∈ Icc q₀ q₁ := by rw [← hI]; exact mem_uvals.2 ⟨x, hx, hpy, rfl⟩
      rw [mem_Icc] at hxu
      simp only [Pi.add_apply, ind, ite_true, if_neg huv]
      omega
    · rintro ⟨h1, h2⟩
      set a := max lo (c - q₁) with ha
      have hca : c - a ∈ uvals u v (draconian G) w := by rw [hI, mem_Icc]; omega
      obtain ⟨x, hx, hpx, hxu⟩ := mem_uvals.1 hca
      refine ⟨x + ind u a + ind v (k - a), mem_mink.2 ⟨x, hx, a, by omega, by omega, rfl⟩, ?_, ?_⟩
      · rw [proj_add_ind_v, proj_add_ind_u, hpx]
      · simp only [Pi.add_apply, ind, ite_true, if_neg huv, hxu]; omega
  rw [this, hI, Nat.card_Icc, Nat.card_Icc]
  omega

/-! ## The Minkowski difference `M⁻` -/

/-- `M⁻(G,uv) = {y : y + e_u ∈ D(G), y + e_v ∈ D(G)}`. -/
def mminus (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Finset (V → ℕ) :=
  ((draconian G).image (fun x => x - ind u 1)).filter
    (fun y => y + ind u 1 ∈ draconian G ∧ y + ind v 1 ∈ draconian G)

lemma mem_mminus {u v : V} {y : V → ℕ} :
    y ∈ mminus G u v ↔ y + ind u 1 ∈ draconian G ∧ y + ind v 1 ∈ draconian G := by
  simp only [mminus, mem_filter, mem_image]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨y + ind u 1, h.1, ?_⟩, h⟩
    funext w; simp [ind]

theorem card_mminus (u v : V) (huv : u ≠ v) :
    (mminus G u v).card + ((draconian G).image (proj u v)).card = (draconian G).card := by
  set W0 := (draconian G).image (proj u v)
  have hsumD : ∀ x ∈ draconian G, ∑ w, x w = Fintype.card V - 1 :=
    fun x hx => (mem_draconian.1 hx).1
  have hN : 2 ≤ Fintype.card V := by
    rw [← card_univ]
    exact one_lt_card.2 ⟨u, mem_univ _, v, mem_univ _, huv⟩
  have hD := card_eq_sum_uvals u v huv (draconian G) _ hsumD W0
    (fun y hy => mem_image_of_mem _ hy)
  have hM := card_eq_sum_uvals u v huv (mminus G u v) (Fintype.card V - 2)
    (by
      intro y hy
      have h := hsumD _ (mem_mminus.1 hy).1
      simp only [Pi.add_apply, sum_add_distrib, sum_ind, mem_univ, ite_true] at h
      omega)
    W0 (by
      intro y hy
      have := mem_image_of_mem (proj u v) (mem_mminus.1 hy).1
      rwa [proj_add_ind_u] at this)
  rw [hM, hD, card_eq_sum_ones W0, ← sum_add_distrib]
  refine sum_congr rfl (fun w hw => ?_)
  obtain ⟨q₀, q₁, hq, hI⟩ := uvals_D_Icc u v huv hw
  have : uvals u v (mminus G u v) w = Ico q₀ q₁ ∧ 1 ≤ q₁ - q₀ + 1 := by
    refine ⟨?_, by omega⟩
    ext c
    rw [mem_uvals, mem_Ico]
    constructor
    · rintro ⟨y, hy, hpy, rfl⟩
      obtain ⟨h1, h2⟩ := mem_mminus.1 hy
      have a1 : (y + ind u 1) u ∈ Icc q₀ q₁ := by
        rw [← hI]; exact mem_uvals.2 ⟨_, h1, by rw [proj_add_ind_u, hpy], rfl⟩
      have a2 : (y + ind v 1) u ∈ Icc q₀ q₁ := by
        rw [← hI]; exact mem_uvals.2 ⟨_, h2, by rw [proj_add_ind_v, hpy], rfl⟩
      simp only [Pi.add_apply, ind, ite_true, if_neg huv, mem_Icc] at a1 a2
      omega
    · rintro ⟨h1, h2⟩
      have hc1 : c + 1 ∈ uvals u v (draconian G) w := by rw [hI, mem_Icc]; omega
      have hc0 : c ∈ uvals u v (draconian G) w := by rw [hI, mem_Icc]; omega
      obtain ⟨x₁, hx₁, hp₁, hu₁⟩ := mem_uvals.1 hc1
      obtain ⟨x₂, hx₂, hp₂, hu₂⟩ := mem_uvals.1 hc0
      have hy1 : x₁ - ind u 1 + ind u 1 = x₁ := by
        funext w'; simp only [ind, Pi.add_apply, Pi.sub_apply]
        split_ifs with h
        · subst h; omega
        · simp
      refine ⟨x₁ - ind u 1, mem_mminus.2 ⟨by rw [hy1]; exact hx₁, ?_⟩, ?_, ?_⟩
      · have : x₁ - ind u 1 + ind v 1 = x₂ := by
          apply eq_of_proj u v huv
          · rw [hsumD x₂ hx₂, ← hsumD x₁ hx₁]
            have e := sum_eq_proj u v huv (x₁ - ind u 1 + ind v 1) univ
            have e1 := sum_eq_proj u v huv x₁ univ
            simp only [mem_univ, ite_true] at e e1
            rw [e, e1]
            have : proj u v (x₁ - ind u 1 + ind v 1) = proj u v x₁ := by
              funext w'; simp only [proj, ind, Pi.add_apply, Pi.sub_apply]
              split_ifs <;> simp_all
            rw [this]
            simp only [Pi.add_apply, Pi.sub_apply, ind, ite_true, if_neg huv, if_neg huv.symm]
            omega
          · funext w'; simp only [proj, ind, Pi.add_apply, Pi.sub_apply]
            rw [← hp₂] at hp₁
            have := congrFun hp₁ w'
            simp only [proj] at this
            split_ifs at this ⊢ <;> simp_all
          · simp only [Pi.add_apply, Pi.sub_apply, ind, ite_true, if_neg huv]; omega
        rw [this]; exact hx₂
      · funext w'; simp only [proj, ind, Pi.sub_apply]
        rw [← hp₁]; simp only [proj]
        split_ifs <;> simp_all
      · simp only [Pi.sub_apply, ind, ite_true]; omega
  rw [this.1, hI, Nat.card_Ico, Nat.card_Icc]
  omega

end Drac
```

### `Glue.lean`

```lean
import FibreCount
import PathBounds
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sum

/-!
# Gluing an ear onto an edge

`glue G u v p` is the graph on `V ⊕ Fin p` obtained from `G` by adding the path
`u — w₀ — w₁ — ⋯ — w_{p-1} — v` (new vertices `w_t = inr t`).  When `uv` is an edge this is
`G ∪_{uv} C_{p+2}`.  We compute its closed neighbourhoods (§2 of the proof):
`|N_H[S_G ⊔ S_W]| = |N_G[S_G] ∪ J(S_W)| + |Ω(σ, S_W)|`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset Ear

namespace Drac

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency of the glued graph. -/
def glueAdj (G : SimpleGraph V) (u v : V) (p : ℕ) : V ⊕ Fin p → V ⊕ Fin p → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr t => (a = u ∧ t.val = 0) ∨ (a = v ∧ t.val + 1 = p)
  | .inr t, .inl a => (a = u ∧ t.val = 0) ∨ (a = v ∧ t.val + 1 = p)
  | .inr s, .inr t => s.val + 1 = t.val ∨ t.val + 1 = s.val

/-- `G` with the ear `u w₀ ⋯ w_{p-1} v` attached. -/
def glue (G : SimpleGraph V) (u v : V) (p : ℕ) : SimpleGraph (V ⊕ Fin p) where
  Adj := glueAdj G u v p
  symm := ⟨fun x y h => by
    cases x with
    | inl a => cases y with
      | inl b => exact G.adj_symm h
      | inr t => exact h
    | inr s => cases y with
      | inl b => exact h
      | inr t => exact Or.comm.1 h⟩
  loopless := ⟨fun x h => by
    cases x with
    | inl a => exact G.irrefl h
    | inr s => simp only [glueAdj] at h; omega⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (p : ℕ) :
    DecidableRel (glue G u v p).Adj := fun x y => by
  cases x <;> cases y <;> (unfold glue glueAdj; infer_instance)

variable {p : ℕ}

/-! ## Positions of ear vertices -/

/-- Ear vertex `w_t` sits at position `t + 1`. -/
def spos (S : Finset (Fin p)) : Finset ℕ := S.image (fun t => t.val + 1)

lemma mem_spos {S : Finset (Fin p)} {n : ℕ} : n ∈ spos S ↔ ∃ t ∈ S, t.val + 1 = n := by
  simp [spos]

lemma succ_mem_spos {S : Finset (Fin p)} {t : Fin p} : t.val + 1 ∈ spos S ↔ t ∈ S := by
  rw [mem_spos]
  constructor
  · rintro ⟨s, hs, h⟩
    rwa [show t = s from Fin.ext (by omega)]
  · exact fun h => ⟨t, h, rfl⟩

lemma spos_sub (S : Finset (Fin p)) : spos S ⊆ Icc 1 p := by
  intro n hn
  obtain ⟨t, -, rfl⟩ := mem_spos.1 hn
  rw [mem_Icc]; omega

/-- Ear vertices at positions in `T`. -/
def sneg (p : ℕ) (T : Finset ℕ) : Finset (Fin p) := univ.filter (fun t => t.val + 1 ∈ T)

lemma spos_sneg {T : Finset ℕ} (hT : T ⊆ Icc 1 p) : spos (sneg p T) = T := by
  ext n
  rw [mem_spos]
  constructor
  · rintro ⟨t, ht, rfl⟩; simpa [sneg] using ht
  · intro hn
    have := mem_Icc.1 (hT hn)
    refine ⟨⟨n - 1, by omega⟩, ?_, by simp; omega⟩
    simp only [sneg, mem_filter, mem_univ, true_and]
    rwa [show n - 1 + 1 = n by omega]

lemma spos_univ : spos (univ : Finset (Fin p)) = Icc 1 p := by
  ext n
  rw [mem_spos, mem_Icc]
  constructor
  · rintro ⟨t, -, rfl⟩; omega
  · intro h; exact ⟨⟨n - 1, by omega⟩, mem_univ _, by simp; omega⟩

/-- Values of the ear coordinates at positions. -/
def zpos (z : Fin p → ℕ) : ℕ → ℕ := fun n => if h : 1 ≤ n ∧ n ≤ p then z ⟨n - 1, by omega⟩ else 0

lemma zpos_succ (z : Fin p → ℕ) (t : Fin p) : zpos z (t.val + 1) = z t := by
  simp [zpos, t.isLt.le]

lemma zs_spos (z : Fin p → ℕ) (S : Finset (Fin p)) : zs (zpos z) (spos S) = ∑ t ∈ S, z t := by
  rw [zs, spos, sum_image (fun a _ b _ h => Fin.ext (by simpa using h))]
  exact sum_congr rfl (fun t _ => zpos_succ z t)

lemma sum_eq_zs (z : Fin p → ℕ) : ∑ t, z t = zs (zpos z) (Icc 1 p) := by
  rw [← spos_univ, zs_spos]

lemma P_eq_sum (z : Fin p → ℕ) : P (zpos z) p = ((∑ t, z t : ℕ) : ℤ) - p := by
  have h := zs_Ioc (zpos z) (Nat.zero_le p)
  have e : Ioc 0 p = Icc 1 p := by ext n; simp; omega
  rw [e, ← sum_eq_zs] at h
  simp at h
  linarith

/-! ## Closed neighbourhoods in the glued graph -/

/-- The part of `{u,v}` adjacent to the ear vertices in `S`. -/
def Jset (u v : V) (S : Finset (Fin p)) : Finset V :=
  (if 1 ∈ spos S then {u} else ∅) ∪ (if p ∈ spos S then {v} else ∅)

/-- The ear part of the closed neighbourhood. -/
def OmH (u v : V) (SG : Finset V) (SW : Finset (Fin p)) : Finset (Fin p) :=
  univ.filter (fun t => t.val + 1 ∈ Om p (decide (u ∈ SG)) (decide (v ∈ SG)) (spos SW))

lemma card_OmH (u v : V) (SG : Finset V) (SW : Finset (Fin p)) :
    (OmH u v SG SW).card = (Om p (decide (u ∈ SG)) (decide (v ∈ SG)) (spos SW)).card := by
  have hsub : Om p (decide (u ∈ SG)) (decide (v ∈ SG)) (spos SW) ⊆ Icc 1 p := filter_subset _ _
  rw [← card_image_of_injective (OmH u v SG SW) (f := fun t : Fin p => t.val + 1)
    (fun a b h => Fin.ext (by simpa using h))]
  congr 1
  ext n
  simp only [OmH, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ht
  · intro hn
    have := mem_Icc.1 (hsub hn)
    exact ⟨⟨n - 1, by omega⟩, by simp only; rwa [show n - 1 + 1 = n by omega], by simp; omega⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

theorem cnbhd_glue (SG : Finset V) (SW : Finset (Fin p)) :
    cnbhd (glue G u v p) (SG.disjSum SW) = (cnbhd G SG ∪ Jset u v SW).disjSum (OmH u v SG SW) := by
  ext x
  rw [mem_cnbhd]
  cases x with
  | inl a =>
    rw [inl_mem_disjSum, inl_mem_disjSum, mem_union, mem_cnbhd]
    constructor
    · rintro (h | ⟨i, hi, hia⟩)
      · exact Or.inl (Or.inl h)
      · rcases i with b | t
        · rw [inl_mem_disjSum] at hi; exact Or.inl (Or.inr ⟨b, hi, hia⟩)
        · rw [inr_mem_disjSum] at hi
          change (a = u ∧ t.val = 0) ∨ (a = v ∧ t.val + 1 = p) at hia
          right
          simp only [Jset, mem_union]
          rcases hia with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
          · left; rw [if_pos (mem_spos.2 ⟨t, hi, by omega⟩)]; simp
          · right; rw [if_pos (mem_spos.2 ⟨t, hi, ht⟩)]; simp
    · rintro ((h | ⟨b, hb, hba⟩) | h)
      · left; exact h
      · right; exact ⟨Sum.inl b, inl_mem_disjSum.2 hb, hba⟩
      · simp only [Jset, mem_union] at h
        rcases h with h | h
        · split_ifs at h with h1
          · rw [mem_singleton] at h; subst h
            obtain ⟨t, ht, ht1⟩ := mem_spos.1 h1
            right; exact ⟨Sum.inr t, inr_mem_disjSum.2 ht, Or.inl ⟨rfl, by omega⟩⟩
          · simp at h
        · split_ifs at h with h1
          · rw [mem_singleton] at h; subst h
            obtain ⟨t, ht, ht1⟩ := mem_spos.1 h1
            right; exact ⟨Sum.inr t, inr_mem_disjSum.2 ht, Or.inr ⟨rfl, ht1⟩⟩
          · simp at h
  | inr t =>
    rw [inr_mem_disjSum, inr_mem_disjSum, OmH, mem_filter]
    simp only [mem_univ, true_and, Om, mem_filter, mem_Icc]
    have ht := t.isLt
    constructor
    · rintro (h | ⟨i, hi, hit⟩)
      · exact ⟨⟨by omega, by omega⟩, Or.inl (succ_mem_spos.2 h)⟩
      · refine ⟨⟨by omega, by omega⟩, ?_⟩
        rcases i with b | s
        · rw [inl_mem_disjSum] at hi
          change (b = u ∧ t.val = 0) ∨ (b = v ∧ t.val + 1 = p) at hit
          rcases hit with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
          · right; right; right; left; exact ⟨by simpa using hi, by omega⟩
          · right; right; right; right; exact ⟨by simpa using hi, h0⟩
        · rw [inr_mem_disjSum] at hi
          change s.val + 1 = t.val ∨ t.val + 1 = s.val at hit
          rcases hit with h0 | h0
          · right; right; left; exact mem_spos.2 ⟨s, hi, by omega⟩
          · right; left; exact mem_spos.2 ⟨s, hi, by omega⟩
    · rintro ⟨-, h | h | h | h | h⟩
      · left; exact succ_mem_spos.1 h
      · obtain ⟨s, hs, hst⟩ := mem_spos.1 h
        right
        refine ⟨Sum.inr s, inr_mem_disjSum.2 hs, ?_⟩
        change s.val + 1 = t.val ∨ t.val + 1 = s.val
        omega
      · obtain ⟨s, hs, hst⟩ := mem_spos.1 h
        right
        refine ⟨Sum.inr s, inr_mem_disjSum.2 hs, ?_⟩
        change s.val + 1 = t.val ∨ t.val + 1 = s.val
        omega
      · obtain ⟨hu, h1⟩ := h
        right
        refine ⟨Sum.inl u, inl_mem_disjSum.2 (by simpa using hu), ?_⟩
        change (u = u ∧ t.val = 0) ∨ (u = v ∧ t.val + 1 = p)
        left; exact ⟨rfl, by omega⟩
      · obtain ⟨hv, h1⟩ := h
        right
        refine ⟨Sum.inl v, inl_mem_disjSum.2 (by simpa using hv), ?_⟩
        change (v = u ∧ t.val = 0) ∨ (v = v ∧ t.val + 1 = p)
        right; exact ⟨rfl, by omega⟩

theorem card_cnbhd_glue (SG : Finset V) (SW : Finset (Fin p)) :
    (cnbhd (glue G u v p) (SG.disjSum SW)).card =
      (cnbhd G SG ∪ Jset u v SW).card + (Om p (decide (u ∈ SG)) (decide (v ∈ SG)) (spos SW)).card := by
  rw [cnbhd_glue, card_disjSum, card_OmH]

/-- Membership in `D(G ∪ ear)` in terms of the two parts `y` (on `V`) and `z` (on the ear). -/
theorem mem_draconian_glue (y : V → ℕ) (z : Fin p → ℕ) :
    Sum.elim y z ∈ draconian (glue G u v p) ↔
      (∑ a, y a + ∑ t, z t = Fintype.card V + p - 1) ∧
      ∀ (SG : Finset V) (SW : Finset (Fin p)), (SG.Nonempty ∨ SW.Nonempty) →
        ∑ a ∈ SG, y a + ∑ t ∈ SW, z t <
          (cnbhd G SG ∪ Jset u v SW).card +
            (Om p (decide (u ∈ SG)) (decide (v ∈ SG)) (spos SW)).card := by
  rw [mem_draconian, IsDraconian, Fintype.card_sum, Fintype.card_fin, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  apply and_congr Iff.rfl
  constructor
  · intro h SG SW hne
    have := h (SG.disjSum SW) (by
      rcases hne with ⟨a, ha⟩ | ⟨t, ht⟩
      · exact ⟨Sum.inl a, by simpa using ha⟩
      · exact ⟨Sum.inr t, by simpa using ht⟩)
    rwa [sum_disjSum, card_cnbhd_glue] at this
  · intro h S hS
    rw [← toLeft_disjSum_toRight (u := S)] at hS ⊢
    rw [sum_disjSum, card_cnbhd_glue]
    simp only [Sum.elim_inl, Sum.elim_inr]
    apply h
    obtain ⟨x, hx⟩ := hS
    rcases x with a | t
    · left; exact ⟨a, by simpa using hx⟩
    · right; exact ⟨t, by simpa using hx⟩

end Drac
```

### `FibreH.lean`

```lean
import Glue

/-!
# The fibres of `D(G ∪_{uv} ear)` over the ear coordinates (Lemmas 2.1–2.3)

For `z` on the ear write `ζ = zpos z`, `T = P ζ p`.
* If some rise of the walk exceeds `1`, or some fall exceeds `2`, or `T ≥ 2`, the fibre is empty.
* If `T ≤ 0` (non-tight), the fibre is `D(G) + {a e_u + (k-a) e_v : k - c_v ≤ a ≤ c_u}`
  with `k = -T` and the explicit `c_u = C10`, `c_v = C01`.
* If `T = 1` (tight) and `uv` is good, the fibre is `M⁻(G,uv)`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset Ear

namespace Drac

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V} {p : ℕ}

/-! ## Bookkeeping lemmas -/

lemma mem_Jset {SW : Finset (Fin p)} {x : V} :
    x ∈ Jset u v SW ↔ (1 ∈ spos SW ∧ x = u) ∨ (p ∈ spos SW ∧ x = v) := by
  simp only [Jset, mem_union]
  constructor
  · rintro (h | h)
    · split_ifs at h with h1
      · exact Or.inl ⟨h1, by simpa using h⟩
      · simp at h
    · split_ifs at h with h1
      · exact Or.inr ⟨h1, by simpa using h⟩
      · simp at h
  · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
    · left; rw [if_pos h1]; simp
    · right; rw [if_pos h1]; simp

lemma card_Jset (huv : u ≠ v) (SW : Finset (Fin p)) :
    (Jset u v SW).card = (if 1 ∈ spos SW then 1 else 0) + (if p ∈ spos SW then 1 else 0) := by
  rw [Jset, card_union_of_disjoint]
  · split_ifs <;> simp
  · split_ifs <;> simp [huv]

lemma Jset_sub_cnbhd (huv : G.Adj u v) {SG : Finset V} (h : u ∈ SG ∨ v ∈ SG)
    (SW : Finset (Fin p)) : Jset u v SW ⊆ cnbhd G SG := by
  have hu : u ∈ cnbhd G SG := by
    rcases h with h | h
    · exact subset_cnbhd _ h
    · exact mem_cnbhd.2 (Or.inr ⟨v, h, huv.symm⟩)
  have hv : v ∈ cnbhd G SG := by
    rcases h with h | h
    · exact mem_cnbhd.2 (Or.inr ⟨u, h, huv⟩)
    · exact subset_cnbhd _ h
  intro x hx
  rcases mem_Jset.1 hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact hu
  · exact hv

lemma card_NP (hp : 1 ≤ p) {T : Finset ℕ} (hT : T ⊆ Icc 1 p) :
    (NP p T).card = (Om p false false T).card + (if 1 ∈ T then 1 else 0)
      + (if p ∈ T then 1 else 0) := by
  have hT' : ∀ t ∈ T, 1 ≤ t ∧ t ≤ p := fun t ht => mem_Icc.1 (hT ht)
  have heq : NP p T = Om p false false T ∪
      ((if 1 ∈ T then {0} else ∅) ∪ (if p ∈ T then {p + 1} else ∅)) := by
    ext t
    simp only [NP, Om, mem_filter, mem_range, mem_union, mem_Icc, Bool.false_eq_true, false_and,
      or_false]
    constructor
    · rintro ⟨ht, h⟩
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · right; left
        rcases h with h | h | ⟨h, _⟩
        · exact absurd (hT' 0 h).1 (by omega)
        · rw [if_pos (by simpa using h)]; simp
        · omega
      · by_cases htp : t ≤ p
        · left
          refine ⟨⟨ht0, htp⟩, ?_⟩
          rcases h with h | h | ⟨_, h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · have htp1 : t = p + 1 := by omega
          subst htp1
          right; right
          rcases h with h | h | ⟨_, h⟩
          · exact absurd (hT' _ h).2 (by omega)
          · exact absurd (hT' _ h).2 (by omega)
          · rw [if_pos (by simpa using h)]; simp
    · rintro (⟨⟨h1, h2⟩, h⟩ | h | h)
      · refine ⟨by omega, ?_⟩
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h1, h⟩)
      · split_ifs at h with h1
        · simp at h; subst h; exact ⟨by omega, Or.inr (Or.inl h1)⟩
        · simp at h
      · split_ifs at h with h1
        · simp at h; subst h; exact ⟨by omega, Or.inr (Or.inr ⟨by omega, by simpa using h1⟩)⟩
        · simp at h
  rw [heq, card_union_of_disjoint, card_union_of_disjoint]
  · split_ifs <;> simp
  · split_ifs <;> simp <;> omega
  · rw [disjoint_union_right]
    constructor
    · split_ifs <;> simp [Om]
    · split_ifs <;> simp [Om]

lemma Om_mono (a b : Bool) (T : Finset ℕ) : Om p false false T ⊆ Om p a b T := by
  intro t ht
  simp only [Om, mem_filter, Bool.false_eq_true, false_and, or_false] at ht ⊢
  exact ⟨ht.1, by tauto⟩

lemma Om10_sub_Om11 (T : Finset ℕ) : Om p true false T ⊆ Om p true true T := by
  intro t ht
  simp only [Om, mem_filter, Bool.false_eq_true, false_and, or_false] at ht ⊢
  exact ⟨ht.1, by tauto⟩

/-- The ear-only constraint `z(S_W) < |N_H[S_W]|` is `ψ ≥ 1`. -/
lemma earOnly_iff (huv : u ≠ v) (hp : 1 ≤ p) (z : Fin p → ℕ) (SW : Finset (Fin p)) :
    (∑ t ∈ SW, z t < (cnbhd G ∅ ∪ Jset u v SW).card +
      (Om p (decide (u ∈ (∅ : Finset V))) (decide (v ∈ (∅ : Finset V))) (spos SW)).card) ↔
      1 ≤ psi p (zpos z) (spos SW) := by
  have h0 : cnbhd G (∅ : Finset V) = ∅ := by ext; simp [mem_cnbhd]
  rw [h0, empty_union, card_Jset huv, psi, card_NP hp (spos_sub SW), zs_spos]
  simp only [notMem_empty, decide_false]
  constructor <;> intro h <;> push_cast <;> split_ifs at h ⊢ <;> omega

/-! ## Necessary conditions -/

variable (G u v)

/-- A nonempty fibre forces every rise of the walk to be at most one. -/
lemma Rc_of_mem (huv : u ≠ v) (hp : 1 ≤ p) {y : V → ℕ} {z : Fin p → ℕ}
    (h : Sum.elim y z ∈ draconian (glue G u v p)) : Rc p (zpos z) := by
  rw [mem_draconian_glue] at h
  intro i j hij hjp
  have hsub : Ioc i j ⊆ Icc 1 p := fun x hx => by simp at hx ⊢; omega
  have h1 := h.2 ∅ (sneg p (Ioc i j)) (Or.inr ⟨⟨j - 1, by omega⟩, by simp [sneg]; omega⟩)
  simp only [sum_empty, zero_add] at h1
  rw [earOnly_iff huv hp, spos_sneg hsub, psi_Ioc _ hij hjp] at h1
  omega

/-- A nonempty fibre gives `φ₁₁(S) ≥ -T` for every ear set `S`. -/
lemma phi11_of_mem (hp : 1 ≤ p) {y : V → ℕ} {z : Fin p → ℕ}
    (h : Sum.elim y z ∈ draconian (glue G u v p)) :
    ∀ T ⊆ Icc 1 p, -P (zpos z) p ≤ phi p true true (zpos z) T := by
  rw [mem_draconian_glue] at h
  intro T hT
  have hne : (univ : Finset V).Nonempty := ⟨u, mem_univ _⟩
  have h1 := h.2 univ (sneg p T) (Or.inl hne)
  have hcn : cnbhd G (univ : Finset V) ∪ Jset u v (sneg p T) = univ :=
    eq_univ_of_forall (fun x => mem_union_left _ (subset_cnbhd _ (mem_univ x)))
  rw [hcn, spos_sneg hT, card_univ] at h1
  simp only [mem_univ, decide_true] at h1
  have e : zs (zpos z) T = ∑ t ∈ sneg p T, z t := by rw [← zs_spos, spos_sneg hT]
  rw [phi, P_eq_sum, e]
  have hs := h.1
  have hN : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
  omega

lemma T_le_one (hp : 1 ≤ p) {z : Fin p → ℕ} (hR : Rc p (zpos z)) : P (zpos z) p ≤ 1 := by
  have := hR 0 p hp le_rfl; simpa using this

lemma Fc_of_mem (huv : u ≠ v) (hp : 1 ≤ p) {y : V → ℕ} {z : Fin p → ℕ}
    (h : Sum.elim y z ∈ draconian (glue G u v p)) : Fc p (zpos z) := by
  intro i j hij hjp
  by_contra hc
  obtain ⟨T, hT, hphi⟩ := wit_fall (z := zpos z) hp hij hjp (by omega)
  have := phi11_of_mem G u v hp h T hT
  omega

/-! ## Non-tight fibres -/

lemma sum_ind_sub (S : Finset V) (y : V → ℕ) (a b : ℕ) (hu : a ≤ y u) (hv : b ≤ y v) (huv : u ≠ v) :
    ∑ w ∈ S, (y - ind u a - ind v b) w + (if u ∈ S then a else 0) + (if v ∈ S then b else 0) =
      ∑ w ∈ S, y w := by
  have : ∀ w, (y - ind u a - ind v b) w + ind u a w + ind v b w = y w := by
    intro w
    simp only [Pi.sub_apply, ind]
    by_cases h1 : w = u
    · subst h1; simp [huv]; omega
    · by_cases h2 : w = v
      · subst h2; simp [h1]; omega
      · simp [h1, h2]
  rw [← sum_ind, ← sum_ind, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun w _ => this w)

/-- The fibre over a non-tight good `z` is `D(G) + segment`. -/
theorem fibre_nontight (huv : G.Adj u v) (hp : 1 ≤ p) {z : Fin p → ℕ}
    (hR : Rc p (zpos z)) (hF : Fc p (zpos z)) (hT : P (zpos z) p ≤ 0) (y : V → ℕ) :
    Sum.elim y z ∈ draconian (glue G u v p) ↔
      y ∈ mink G u v (p - ∑ t, z t) ((p - ∑ t, z t) - (C01 p (zpos z)).toNat)
        (C10 p (zpos z)).toNat := by
  have hne : u ≠ v := huv.ne
  have hPs := P_eq_sum z
  have hzp : ∑ t, z t ≤ p := by omega
  set k := p - ∑ t, z t with hk
  have hTk : P (zpos z) p = -(k : ℤ) := by omega
  have c10a := @C10_nonneg p (zpos z)
  have c10b := @C10_le_one p (zpos z)
  have c01a := @C01_nonneg p (zpos z)
  have c01b := @C01_le_one p (zpos z)
  have hsum := Csum hR hF hT
  have hc10k : C10 p (zpos z) ≤ k := by
    unfold C10; split_ifs with h
    · omega
    · omega
  have hc01k : C01 p (zpos z) ≤ k := by
    unfold C01; split_ifs with h
    · omega
    · omega
  have LB := lb_main hR hT hp
  have LB11 := lb11 hR hF hT hp
  have hN2 : 2 ≤ Fintype.card V := by
    rw [← card_univ]; exact one_lt_card.2 ⟨u, mem_univ _, v, mem_univ _, hne⟩
  rw [mem_draconian_glue, mem_mink]
  constructor
  · -- (⊆): find the segment parameter
    rintro ⟨hs, hS⟩
    have hsy : ∑ a, y a = Fintype.card V - 1 + k := by omega
    -- type (1,0)
    have Fu : ∀ S : Finset V, u ∈ S → v ∉ S →
        ((∑ a ∈ S, y a : ℕ) : ℤ) - ((cnbhd G S).card : ℤ) + 1 ≤ C10 p (zpos z) := by
      intro S hu hv
      obtain ⟨T, hTsub, hTphi⟩ := wit10 hT hp (z := zpos z)
      have h1 := hS S (sneg p T) (Or.inl ⟨u, hu⟩)
      rw [show cnbhd G S ∪ Jset u v (sneg p T) = cnbhd G S from
        union_eq_left.2 (Jset_sub_cnbhd huv (Or.inl hu) _), spos_sneg hTsub] at h1
      simp only [hu, hv, decide_true, decide_false] at h1
      have e : zs (zpos z) T = ∑ t ∈ sneg p T, z t := by rw [← zs_spos, spos_sneg hTsub]
      rw [phi, e] at hTphi
      omega
    have Fv : ∀ S : Finset V, v ∈ S → u ∉ S →
        ((∑ a ∈ S, y a : ℕ) : ℤ) - ((cnbhd G S).card : ℤ) + 1 ≤ C01 p (zpos z) := by
      intro S hv hu
      obtain ⟨T, hTsub, hTphi⟩ := wit01 hT hp (z := zpos z)
      have h1 := hS S (sneg p T) (Or.inl ⟨v, hv⟩)
      rw [show cnbhd G S ∪ Jset u v (sneg p T) = cnbhd G S from
        union_eq_left.2 (Jset_sub_cnbhd huv (Or.inr hv) _), spos_sneg hTsub] at h1
      simp only [hu, hv, decide_true, decide_false] at h1
      have e : zs (zpos z) T = ∑ t ∈ sneg p T, z t := by rw [← zs_spos, spos_sneg hTsub]
      rw [phi, e] at hTphi
      omega
    have Fuv : ∀ S : Finset V, u ∈ S → v ∈ S →
        ∑ a ∈ S, y a + 1 ≤ (cnbhd G S).card + k := by
      intro S hu hv
      have h1 := hS S univ (Or.inl ⟨u, hu⟩)
      rw [show cnbhd G S ∪ Jset u v (univ : Finset (Fin p)) = cnbhd G S from
        union_eq_left.2 (Jset_sub_cnbhd huv (Or.inl hu) _), spos_univ] at h1
      simp only [hu, hv, decide_true] at h1
      have hW : Om p true true (Icc 1 p) = Icc 1 p := by
        ext t; simp only [Om, mem_filter, mem_Icc]; constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, Or.inl h⟩
      rw [hW, Nat.card_Icc] at h1
      omega
    have F0 : ∀ S : Finset V, S.Nonempty → u ∉ S → v ∉ S →
        ∑ a ∈ S, y a + 1 ≤ (cnbhd G S).card := by
      intro S hSne hu hv
      have h1 := hS S ∅ (Or.inl hSne)
      have hJ : Jset u v (∅ : Finset (Fin p)) = ∅ := by
        ext x; simp [mem_Jset, spos]
      have hO : Om p (decide (u ∈ S)) (decide (v ∈ S)) (spos (∅ : Finset (Fin p))) = ∅ := by
        ext t; simp [Om, spos, hu, hv]
      rw [hJ, hO] at h1
      simpa using h1
    -- the maxima L_u, L_v
    set Su := (univ : Finset (Finset V)).filter (fun S => u ∈ S ∧ v ∉ S) with hSu
    set Sv := (univ : Finset (Finset V)).filter (fun S => v ∈ S ∧ u ∉ S) with hSv
    have hSune : Su.Nonempty := ⟨{u}, by simp [hSu, hne.symm]⟩
    have hSvne : Sv.Nonempty := ⟨{v}, by simp [hSv, hne]⟩
    set fL : Finset V → ℤ := fun S => ((∑ a ∈ S, y a : ℕ) : ℤ) - ((cnbhd G S).card : ℤ) + 1
      with hfL
    set Lu := Su.sup' hSune fL
    set Lv := Sv.sup' hSvne fL
    have hLu : ∀ S, u ∈ S → v ∉ S → fL S ≤ Lu := fun S h1 h2 =>
      le_sup' fL (by simp [hSu, h1, h2])
    have hLv : ∀ S, v ∈ S → u ∉ S → fL S ≤ Lv := fun S h1 h2 =>
      le_sup' fL (by simp [hSv, h1, h2])
    obtain ⟨Su0, hSu0, hLuEq⟩ := exists_mem_eq_sup' hSune fL
    obtain ⟨Sv0, hSv0, hLvEq⟩ := exists_mem_eq_sup' hSvne fL
    simp only [hSu, hSv, mem_filter, mem_univ, true_and] at hSu0 hSv0
    replace hLuEq : Lu = fL Su0 := hLuEq
    replace hLvEq : Lv = fL Sv0 := hLvEq
    -- the nine inequalities
    have i1 : Lu ≤ C10 p (zpos z) := by rw [hLuEq]; exact Fu Su0 hSu0.1 hSu0.2
    have i2 : Lv ≤ C01 p (zpos z) := by rw [hLvEq]; exact Fv Sv0 hSv0.1 hSv0.2
    have i3 : Lu ≤ y u := by
      rw [hLuEq]
      simp only [hfL]
      have hs' := add_sum_erase Su0 y hSu0.1
      by_cases he : (Su0.erase u).Nonempty
      · have := F0 (Su0.erase u) he (notMem_erase u _) (fun h => hSu0.2 (mem_of_mem_erase h))
        have hc := card_le_card (cnbhd_mono (G := G) (erase_subset u Su0))
        omega
      · rw [not_nonempty_iff_eq_empty] at he
        rw [he, sum_empty] at hs'
        have := card_cnbhd_pos (G := G) ⟨u, hSu0.1⟩
        omega
    have i4 : Lv ≤ y v := by
      rw [hLvEq]
      simp only [hfL]
      have hs' := add_sum_erase Sv0 y hSv0.1
      by_cases he : (Sv0.erase v).Nonempty
      · have := F0 (Sv0.erase v) he (fun h => hSv0.2 (mem_of_mem_erase h)) (notMem_erase v _)
        have hc := card_le_card (cnbhd_mono (G := G) (erase_subset v Sv0))
        omega
      · rw [not_nonempty_iff_eq_empty] at he
        rw [he, sum_empty] at hs'
        have := card_cnbhd_pos (G := G) ⟨v, hSv0.1⟩
        omega
    have i5 : Lu + Lv ≤ k := by
      rw [hLuEq, hLvEq]
      simp only [hfL]
      have hsm := card_cnbhd_submod (G := G) Su0 Sv0
      have hsy' := sum_union_inter (s₁ := Su0) (s₂ := Sv0) (f := y)
      have hU := Fuv (Su0 ∪ Sv0) (mem_union_left _ hSu0.1) (mem_union_right _ hSv0.1)
      by_cases hI : (Su0 ∩ Sv0).Nonempty
      · have hI' := F0 (Su0 ∩ Sv0) hI (fun h => hSv0.2 (mem_inter.1 h).2)
          (fun h => hSu0.2 (mem_inter.1 h).1)
        omega
      · rw [not_nonempty_iff_eq_empty] at hI
        rw [hI, sum_empty, add_zero] at hsy'
        have hvU : v ∈ cnbhd G Su0 ∩ cnbhd G Sv0 :=
          mem_inter.2 ⟨mem_cnbhd.2 (Or.inr ⟨u, hSu0.1, huv⟩), subset_cnbhd _ hSv0.1⟩
        have hcu := card_union_add_card_inter (cnbhd G Su0) (cnbhd G Sv0)
        have hpos : 1 ≤ (cnbhd G Su0 ∩ cnbhd G Sv0).card := card_pos.2 ⟨v, hvU⟩
        rw [← cnbhd_union] at hcu
        omega
    have i6 : (k : ℤ) - C01 p (zpos z) ≤ y u := by
      have h1 := Fv (univ.erase u) (mem_erase.2 ⟨hne.symm, mem_univ _⟩) (notMem_erase u _)
      have hc := card_cnbhd_le (G := G) (univ.erase u)
      have hs' := add_sum_erase univ y (mem_univ u)
      omega
    have i7 : (k : ℤ) - C10 p (zpos z) ≤ y v := by
      have h1 := Fu (univ.erase v) (mem_erase.2 ⟨hne, mem_univ _⟩) (notMem_erase v _)
      have hc := card_cnbhd_le (G := G) (univ.erase v)
      have hs' := add_sum_erase univ y (mem_univ v)
      omega
    have i8 : k ≤ y u + y v := by
      have hs' := add_sum_erase univ y (mem_univ u)
      have hs'' := add_sum_erase (univ.erase u) y (mem_erase.2 ⟨hne.symm, mem_univ v⟩)
      have hrest : ∑ a ∈ (univ.erase u).erase v, y a ≤ Fintype.card V - 1 := by
        by_cases hr : ((univ.erase u).erase v).Nonempty
        · have := F0 _ hr (fun h => by simp at h) (fun h => by simp at h)
          have := card_cnbhd_le (G := G) ((univ.erase u).erase v)
          omega
        · rw [not_nonempty_iff_eq_empty] at hr; rw [hr]; simp
      omega
    -- choose `a`
    set a : ℤ := max (max ((k : ℤ) - C01 p (zpos z)) ((k : ℤ) - y v)) Lu with ha
    have ha1 : (k : ℤ) - C01 p (zpos z) ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
    have ha2 : (k : ℤ) - y v ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
    have ha3 : Lu ≤ a := le_max_right _ _
    have hau : a ≤ C10 p (zpos z) := max_le (max_le (by omega) (by omega)) i1
    have hau' : a ≤ y u := max_le (max_le i6 (by omega)) i3
    have hav : a ≤ k - Lv := max_le (max_le (by omega) (by omega)) (by omega)
    have ha0 : 0 ≤ a := by omega
    set an := a.toNat with han
    have hanz : (an : ℤ) = a := Int.toNat_of_nonneg ha0
    have hanu : an ≤ y u := by omega
    have hanv : k - an ≤ y v := by omega
    have hank : an ≤ k := by omega
    refine ⟨y - ind u an - ind v (k - an), ?_, an, ?_, ?_, ?_⟩
    · rw [mem_draconian]
      refine ⟨?_, fun S hSne => ?_⟩
      · have := sum_ind_sub (u := u) (v := v) univ y an (k - an) hanu hanv hne
        simp only [mem_univ, ite_true] at this
        omega
      · have e := sum_ind_sub (u := u) (v := v) S y an (k - an) hanu hanv hne
        by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
        · have := Fuv S hu hv; simp only [hu, hv, ite_true] at e; omega
        · have := hLu S hu hv; simp only [hfL] at this; simp only [hu, hv, ite_true, ite_false] at e
          omega
        · have := hLv S hv hu; simp only [hfL] at this; simp only [hu, hv, ite_true, ite_false] at e
          omega
        · have := F0 S hSne hu hv; simp only [hu, hv, ite_false] at e; omega
    · omega
    · omega
    · funext w
      simp only [Pi.add_apply, Pi.sub_apply, ind]
      by_cases h1 : w = u
      · subst h1; simp [hne]; omega
      · by_cases h2 : w = v
        · subst h2; simp [h1]; omega
        · simp [h1, h2]
  · -- (⊇)
    rintro ⟨x, hx, a, ha1, ha2, rfl⟩
    rw [mem_draconian] at hx
    have hak : a ≤ k := by omega
    have ha1' : (k : ℤ) - C01 p (zpos z) ≤ a := by omega
    have ha2' : (a : ℤ) ≤ C10 p (zpos z) := by omega
    refine ⟨?_, fun SG SW hne' => ?_⟩
    · simp only [Pi.add_apply, sum_add_distrib, sum_ind, mem_univ, ite_true, hx.1]
      omega
    · have hsub := spos_sub SW
      by_cases hSG : SG.Nonempty
      · have hx' := hx.2 SG hSG
        have e : ∑ w ∈ SG, (x + ind u a + ind v (k - a)) w =
            ∑ w ∈ SG, x w + (if u ∈ SG then a else 0) + (if v ∈ SG then k - a else 0) := by
          simp only [Pi.add_apply, sum_add_distrib, sum_ind]
        rw [e]
        by_cases hu : u ∈ SG <;> by_cases hv : v ∈ SG
        · rw [union_eq_left.2 (Jset_sub_cnbhd huv (Or.inl hu) _)]
          have := LB11 _ hsub
          rw [phi, zs_spos] at this
          simp only [hu, hv, decide_true, ite_true] at this ⊢
          omega
        · rw [union_eq_left.2 (Jset_sub_cnbhd huv (Or.inl hu) _)]
          have := (LB _ hsub).2.1
          rw [phi, zs_spos] at this
          simp only [hu, hv, decide_true, decide_false, ite_true, ite_false] at this ⊢
          omega
        · rw [union_eq_left.2 (Jset_sub_cnbhd huv (Or.inr hv) _)]
          have := (LB _ hsub).2.2
          rw [phi, zs_spos] at this
          simp only [hu, hv, decide_true, decide_false, ite_true, ite_false] at this ⊢
          omega
        · have := (LB _ hsub).1
          rw [phi, zs_spos] at this
          have hc := card_le_card (subset_union_left (s₁ := cnbhd G SG) (s₂ := Jset u v SW))
          simp only [hu, hv, decide_false, ite_false] at this ⊢
          omega
      · rw [not_nonempty_iff_eq_empty] at hSG
        subst hSG
        have hSW : SW.Nonempty := by
          rcases hne' with h | h
          · simp at h
          · exact h
        have := lb_psi hR _ hsub (by
          obtain ⟨t, ht⟩ := hSW; exact ⟨t.val + 1, succ_mem_spos.2 ht⟩)
        have h2 := (earOnly_iff (G := G) hne hp z SW).2 this
        simpa using h2

/-! ## Tight fibres -/

/-- `uv` is *good* (δ(G,uv) = 0): the Minkowski difference has no extra constraints. -/
def Good (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : Prop :=
  ∀ y : V → ℕ, y + ind u 1 ∈ draconian G → y + ind v 1 ∈ draconian G →
    ∀ S : Finset V, S.Nonempty → u ∉ S → v ∉ S → u ∈ cnbhd G S → v ∈ cnbhd G S →
      ∑ a ∈ S, y a + 2 ≤ (cnbhd G S).card

theorem fibre_tight (huv : G.Adj u v) (hgood : Good G u v) (hp : 1 ≤ p) {z : Fin p → ℕ}
    (hR : Rc p (zpos z)) (hT : P (zpos z) p = 1) (y : V → ℕ) :
    Sum.elim y z ∈ draconian (glue G u v p) ↔ y ∈ mminus G u v := by
  have hne : u ≠ v := huv.ne
  have hsz : ∑ t, z t = p + 1 := by have := P_eq_sum z; omega
  have hN2 : 2 ≤ Fintype.card V := by
    rw [← card_univ]; exact one_lt_card.2 ⟨u, mem_univ _, v, mem_univ _, hne⟩
  have hW : Om p true true (Icc 1 p) = Icc 1 p := by
    ext t; simp only [Om, mem_filter, mem_Icc]; constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, Or.inl h⟩
  have hOmW : ∀ a b : Bool, (a = true ∨ b = true) → Om p a b (Icc 1 p) = Icc 1 p := by
    intro a b _
    ext t; simp only [Om, mem_filter, mem_Icc]; constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, Or.inl h⟩
  rw [mem_draconian_glue, mem_mminus, mem_draconian, mem_draconian]
  constructor
  · rintro ⟨hs, hS⟩
    have hsy : ∑ a, y a = Fintype.card V - 2 := by omega
    have key : ∀ S : Finset V, S.Nonempty → (u ∈ S ∨ v ∈ S) → ∑ a ∈ S, y a + 2 ≤ (cnbhd G S).card := by
      intro S hSne huvS
      have h1 := hS S univ (Or.inl hSne)
      rw [union_eq_left.2 (Jset_sub_cnbhd huv huvS _), spos_univ,
        hOmW _ _ (by rcases huvS with h | h <;> simp [h]), Nat.card_Icc] at h1
      omega
    have key0 : ∀ S : Finset V, S.Nonempty → ∑ a ∈ S, y a + 1 ≤ (cnbhd G S).card := by
      intro S hSne
      by_cases huvS : u ∈ S ∨ v ∈ S
      · have := key S hSne huvS; omega
      · push Not at huvS
        have h1 := hS S ∅ (Or.inl hSne)
        have hJ : Jset u v (∅ : Finset (Fin p)) = ∅ := by ext x; simp [mem_Jset, spos]
        have hO : Om p (decide (u ∈ S)) (decide (v ∈ S)) (spos (∅ : Finset (Fin p))) = ∅ := by
          ext t; simp [Om, spos, huvS.1, huvS.2]
        rw [hJ, hO] at h1
        simpa using h1
    refine ⟨⟨?_, fun S hSne => ?_⟩, ⟨?_, fun S hSne => ?_⟩⟩
    · simp only [Pi.add_apply, sum_add_distrib, sum_ind, mem_univ, ite_true]; omega
    · simp only [Pi.add_apply, sum_add_distrib, sum_ind]
      by_cases hu : u ∈ S
      · have := key S hSne (Or.inl hu); simp only [hu, ite_true]; omega
      · have := key0 S hSne; simp only [hu, ite_false]; omega
    · simp only [Pi.add_apply, sum_add_distrib, sum_ind, mem_univ, ite_true]; omega
    · simp only [Pi.add_apply, sum_add_distrib, sum_ind]
      by_cases hv : v ∈ S
      · have := key S hSne (Or.inr hv); simp only [hv, ite_true]; omega
      · have := key0 S hSne; simp only [hv, ite_false]; omega
  · rintro ⟨⟨hsu, hSu⟩, ⟨hsv, hSv⟩⟩
    have hsy : ∑ a, y a + 1 = Fintype.card V - 1 := by
      simp only [Pi.add_apply, sum_add_distrib, sum_ind, mem_univ, ite_true] at hsu; omega
    refine ⟨by omega, fun SG SW hne' => ?_⟩
    have hsub := spos_sub SW
    -- the ear part is bounded by `ψ`
    have hzs : ∑ t ∈ SW, z t + 1 ≤ (Jset u v SW).card + (Om p false false (spos SW)).card ∨
        ∑ t ∈ SW, z t = 0 := by
      by_cases hSW : SW.Nonempty
      · left
        have := lb_psi hR _ hsub (by
          obtain ⟨t, ht⟩ := hSW; exact ⟨t.val + 1, succ_mem_spos.2 ht⟩)
        rw [psi, card_NP hp hsub, zs_spos] at this
        rw [card_Jset hne]
        split_ifs at this ⊢ <;> omega
      · right; rw [not_nonempty_iff_eq_empty] at hSW; subst hSW; simp
    have hJ2 : (Jset u v SW).card ≤ 2 := by rw [card_Jset hne]; split_ifs <;> simp
    have hOm := card_le_card (Om_mono (p := p) (decide (u ∈ SG)) (decide (v ∈ SG)) (spos SW))
    by_cases hSG : SG.Nonempty
    · have eu := hSu SG hSG
      have ev := hSv SG hSG
      simp only [Pi.add_apply, sum_add_distrib, sum_ind] at eu ev
      by_cases huvS : u ∈ SG ∨ v ∈ SG
      · rw [union_eq_left.2 (Jset_sub_cnbhd huv huvS _)]
        rcases huvS with hu | hv
        · simp only [hu, ite_true] at eu; omega
        · simp only [hv, ite_true] at ev; omega
      · push Not at huvS
        simp only [huvS.1, huvS.2, ite_false, add_zero] at eu ev
        by_cases hboth : u ∈ cnbhd G SG ∧ v ∈ cnbhd G SG
        · have := hgood y (by rw [mem_draconian]; exact ⟨hsu, hSu⟩)
            (by rw [mem_draconian]; exact ⟨hsv, hSv⟩) SG hSG huvS.1 huvS.2 hboth.1 hboth.2
          have hc := card_le_card (subset_union_left (s₁ := cnbhd G SG) (s₂ := Jset u v SW))
          simp only [huvS.1, huvS.2, decide_false] at hOm ⊢
          omega
        · -- at most one element of `J` is already in `N[SG]`
          have hJc : (Jset u v SW).card ≤ (Jset u v SW \ cnbhd G SG).card + 1 := by
            have h1 : (Jset u v SW ∩ cnbhd G SG).card ≤ 1 := by
              rw [card_le_one]
              intro a ha b hb
              rcases mem_Jset.1 (mem_inter.1 ha).1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
                rcases mem_Jset.1 (mem_inter.1 hb).1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
              · rfl
              · exact absurd ⟨(mem_inter.1 ha).2, (mem_inter.1 hb).2⟩ hboth
              · exact absurd ⟨(mem_inter.1 hb).2, (mem_inter.1 ha).2⟩ hboth
              · rfl
            have := card_sdiff_add_card_inter (Jset u v SW) (cnbhd G SG)
            omega
          have hcu : (cnbhd G SG ∪ Jset u v SW).card =
              (cnbhd G SG).card + (Jset u v SW \ cnbhd G SG).card := by
            rw [← union_sdiff_self_eq_union, card_union_of_disjoint disjoint_sdiff]
          simp only [huvS.1, huvS.2, decide_false] at ⊢
          rw [hcu]
          omega
    · rw [not_nonempty_iff_eq_empty] at hSG
      subst hSG
      have hSW : SW.Nonempty := by
        rcases hne' with h | h
        · simp at h
        · exact h
      have := lb_psi hR _ hsub (by
        obtain ⟨t, ht⟩ := hSW; exact ⟨t.val + 1, succ_mem_spos.2 ht⟩)
      have h2 := (earOnly_iff (G := G) hne hp z SW).2 this
      simpa using h2

end Drac
```

### `WordCount.lean`

```lean
import Glue
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# Counting ear words (the path constants of §3)

`Z p` is the set of ear vectors `z : Fin p → {0,1,2}`.  We count
* the words all of whose rises are `≤ 1` and falls are `≤ 2`: `(p+2) 2^{p-1}` of them;
* the tight words (`T = 1`): `2^{p-1}`;
* `∑ (c_u + c_v - k)` over the non-tight good words: `2^{p-1}`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset Ear

namespace Drac

open scoped Classical

/-- Ear vectors with entries in `{0,1,2}`. -/
def Z (p : ℕ) : Finset (Fin p → ℕ) := Fintype.piFinset (fun _ => range 3)

/-- Append a coordinate. -/
def snoc' {p : ℕ} (w : Fin p → ℕ) (c : ℕ) : Fin (p + 1) → ℕ := Fin.snoc (α := fun _ => ℕ) w c

lemma zpos_snoc_le {p : ℕ} (w : Fin p → ℕ) (c : ℕ) {n : ℕ} (hn : n ≤ p) :
    zpos (snoc' w c) n = zpos w n := by
  unfold zpos snoc'
  by_cases h : 1 ≤ n
  · rw [dif_pos ⟨h, by omega⟩, dif_pos ⟨h, hn⟩]
    simp [Fin.snoc, show n - 1 < p by omega]
  · rw [dif_neg (by omega), dif_neg (by omega)]

lemma zpos_snoc_last {p : ℕ} (w : Fin p → ℕ) (c : ℕ) : zpos (snoc' w c) (p + 1) = c := by
  unfold zpos snoc'
  rw [dif_pos ⟨by omega, le_rfl⟩]
  simp [Fin.snoc]

lemma P_snoc_le {p : ℕ} (w : Fin p → ℕ) (c : ℕ) {j : ℕ} (hj : j ≤ p) :
    P (zpos (snoc' w c)) j = P (zpos w) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [P_succ, P_succ, ih (by omega), zpos_snoc_le w c hj]

lemma P_snoc_last {p : ℕ} (w : Fin p → ℕ) (c : ℕ) :
    P (zpos (snoc' w c)) (p + 1) = P (zpos w) p + c - 1 := by
  rw [P_succ, P_snoc_le w c le_rfl, zpos_snoc_last]

lemma card_Z_succ {p : ℕ} (Q : (Fin (p + 1) → ℕ) → Prop) [DecidablePred Q] :
    ((Z (p + 1)).filter Q).card = ∑ c ∈ range 3, ((Z p).filter (fun w => Q (snoc' w c))).card := by
  rw [card_eq_sum_card_fiberwise (f := fun z => z (Fin.last p)) (t := range 3)]
  · refine sum_congr rfl (fun c hc => ?_)
    apply card_nbij' (fun z => Fin.init z) (fun w => snoc' w c)
    · intro z hz
      rw [mem_coe, mem_filter, mem_filter] at hz
      rw [mem_coe, mem_filter]
      obtain ⟨⟨h1, h2⟩, h3⟩ := hz
      have hzs : snoc' (Fin.init z) c = z := by
        rw [← h3]; exact Fin.snoc_init_self z
      refine ⟨?_, by rw [hzs]; exact h2⟩
      rw [Z, Fintype.mem_piFinset] at h1 ⊢
      intro i; exact h1 _
    · intro w hw
      rw [mem_coe, mem_filter] at hw
      rw [mem_coe, mem_filter, mem_filter]
      refine ⟨⟨?_, hw.2⟩, by simp [snoc']⟩
      have h1 := hw.1
      rw [Z, Fintype.mem_piFinset] at h1 ⊢
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [snoc']; simpa using hc
      · simp [snoc']; simpa using h1 j
    · intro z hz
      rw [mem_coe, mem_filter] at hz
      rw [← hz.2]; exact Fin.snoc_init_self z
    · intro w _; simp [snoc']
  · intro z hz
    rw [mem_coe, mem_filter, Z, Fintype.mem_piFinset] at hz
    rw [mem_coe]
    exact hz.1 _

/-! ## Walk minimum and maximum -/

variable {p : ℕ}

/-- Minimum of the walk `P 0, …, P p`. -/
def wlo (p : ℕ) (z : ℕ → ℕ) : ℤ := (range (p + 1)).inf' nonempty_range_add_one (P z)
/-- Maximum of the walk. -/
def whi (p : ℕ) (z : ℕ → ℕ) : ℤ := (range (p + 1)).sup' nonempty_range_add_one (P z)

lemma wlo_le (z : ℕ → ℕ) {j : ℕ} (hj : j ≤ p) : wlo p z ≤ P z j :=
  inf'_le _ (mem_range.2 (by omega))
lemma le_whi (z : ℕ → ℕ) {j : ℕ} (hj : j ≤ p) : P z j ≤ whi p z :=
  le_sup' _ (mem_range.2 (by omega))
lemma wlo_attained (z : ℕ → ℕ) : ∃ j ≤ p, P z j = wlo p z := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_inf' (nonempty_range_add_one (n := p)) (P z)
  exact ⟨j, by rw [mem_range] at hj; omega, h.symm⟩
lemma whi_attained (z : ℕ → ℕ) : ∃ j ≤ p, P z j = whi p z := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_sup' (nonempty_range_add_one (n := p)) (P z)
  exact ⟨j, by rw [mem_range] at hj; omega, h.symm⟩

lemma wlo_snoc (w : Fin p → ℕ) (c : ℕ) :
    wlo (p + 1) (zpos (snoc' w c)) = min (wlo p (zpos w)) (P (zpos w) p + c - 1) := by
  apply le_antisymm
  · apply le_min
    · obtain ⟨j, hj, h⟩ := wlo_attained (p := p) (zpos w)
      rw [← h, ← P_snoc_le w c hj]; exact wlo_le _ (by omega)
    · rw [← P_snoc_last]; exact wlo_le _ le_rfl
  · obtain ⟨j, hj, h⟩ := wlo_attained (p := p + 1) (zpos (snoc' w c))
    rw [← h]
    rcases eq_or_lt_of_le hj with rfl | hj'
    · rw [P_snoc_last]; exact min_le_right _ _
    · rw [P_snoc_le w c (by omega)]; exact (min_le_left _ _).trans (wlo_le _ (by omega))

lemma whi_snoc (w : Fin p → ℕ) (c : ℕ) :
    whi (p + 1) (zpos (snoc' w c)) = max (whi p (zpos w)) (P (zpos w) p + c - 1) := by
  apply le_antisymm
  · obtain ⟨j, hj, h⟩ := whi_attained (p := p + 1) (zpos (snoc' w c))
    rw [← h]
    rcases eq_or_lt_of_le hj with rfl | hj'
    · rw [P_snoc_last]; exact le_max_right _ _
    · rw [P_snoc_le w c (by omega)]; exact (le_whi _ (by omega)).trans (le_max_left _ _)
  · apply max_le
    · obtain ⟨j, hj, h⟩ := whi_attained (p := p) (zpos w)
      rw [← h, ← P_snoc_le w c hj]; exact le_whi _ (by omega)
    · rw [← P_snoc_last]; exact le_whi _ le_rfl

/-- State of a walk: `(T - min, max - T)`. -/
def st (p : ℕ) (z : ℕ → ℕ) : ℤ × ℤ := (P z p - wlo p z, whi p z - P z p)

lemma Rc_snoc (w : Fin p → ℕ) (c : ℕ) :
    Rc (p + 1) (zpos (snoc' w c)) ↔ Rc p (zpos w) ∧ (st p (zpos w)).1 + c - 1 ≤ 1 := by
  simp only [st]
  constructor
  · intro h
    refine ⟨fun i j hij hjp => ?_, ?_⟩
    · have := h i j hij (by omega)
      rwa [P_snoc_le w c hjp, P_snoc_le w c (by omega)] at this
    · obtain ⟨i, hi, hie⟩ := wlo_attained (p := p) (zpos w)
      have := h i (p + 1) (by omega) le_rfl
      rw [P_snoc_last, P_snoc_le w c hi] at this
      omega
  · rintro ⟨h1, h2⟩ i j hij hjp
    rcases eq_or_lt_of_le hjp with rfl | hj
    · rw [P_snoc_last, P_snoc_le w c (by omega)]
      have := wlo_le (p := p) (zpos w) (j := i) (by omega)
      omega
    · rw [P_snoc_le w c (by omega), P_snoc_le w c (by omega)]
      exact h1 i j hij (by omega)

lemma Fc_snoc (w : Fin p → ℕ) (c : ℕ) :
    Fc (p + 1) (zpos (snoc' w c)) ↔ Fc p (zpos w) ∧ (st p (zpos w)).2 - c + 1 ≤ 2 := by
  simp only [st]
  constructor
  · intro h
    refine ⟨fun i j hij hjp => ?_, ?_⟩
    · have := h i j hij (by omega)
      rwa [P_snoc_le w c hjp, P_snoc_le w c (by omega)] at this
    · obtain ⟨i, hi, hie⟩ := whi_attained (p := p) (zpos w)
      have := h i (p + 1) (by omega) le_rfl
      rw [P_snoc_last, P_snoc_le w c hi] at this
      omega
  · rintro ⟨h1, h2⟩ i j hij hjp
    rcases eq_or_lt_of_le hjp with rfl | hj
    · rw [P_snoc_last, P_snoc_le w c (by omega)]
      have := le_whi (p := p) (zpos w) (j := i) (by omega)
      omega
    · rw [P_snoc_le w c (by omega), P_snoc_le w c (by omega)]
      exact h1 i j hij (by omega)

lemma st_snoc (w : Fin p → ℕ) (c : ℕ) :
    st (p + 1) (zpos (snoc' w c)) =
      (max ((st p (zpos w)).1 + c - 1) 0, max ((st p (zpos w)).2 - c + 1) 0) := by
  simp only [st, wlo_snoc, whi_snoc, P_snoc_last, Prod.mk.injEq]
  constructor
  · rcases le_total (wlo p (zpos w)) (P (zpos w) p + c - 1) with h | h
    · rw [min_eq_left h, max_eq_left (by omega)]; ring
    · rw [min_eq_right h, max_eq_right (by omega)]; ring
  · rcases le_total (whi p (zpos w)) (P (zpos w) p + c - 1) with h | h
    · rw [max_eq_right h, max_eq_right (by omega)]; ring
    · rw [max_eq_left h, max_eq_left (by omega)]; ring

/-- The five reachable states. -/
def States : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1), (0, 2), (1, 1)}

lemma st_mem (z : ℕ → ℕ) (hR : Rc p z) (hF : Fc p z) : st p z ∈ States := by
  obtain ⟨i, hi, hie⟩ := wlo_attained (p := p) z
  obtain ⟨j, hj, hje⟩ := whi_attained (p := p) z
  have a1 := wlo_le (p := p) z (le_refl p)
  have a2 := le_whi (p := p) z (le_refl p)
  have hα : P z p - wlo p z ≤ 1 := by
    rcases eq_or_lt_of_le hi with rfl | hi'
    · omega
    · have := hR i p hi' le_rfl; omega
  have hβ : whi p z - P z p ≤ 2 := by
    rcases eq_or_lt_of_le hj with rfl | hj'
    · omega
    · have := hF j p hj' le_rfl; omega
  have hrange : whi p z - wlo p z ≤ 2 := by
    rcases lt_trichotomy i j with h | rfl | h
    · have := hR i j h hj; omega
    · omega
    · have := hF j i h hi; omega
  simp only [States, st, mem_insert, mem_singleton, Prod.mk.injEq]
  omega

/-- Counts by state. -/
noncomputable def Fs (p : ℕ) (s : ℤ × ℤ) : ℕ :=
  ((Z p).filter (fun z => Rc p (zpos z) ∧ Fc p (zpos z) ∧ st p (zpos z) = s)).card

open scoped Classical in
lemma card_by_state (φ : ℤ × ℤ → Prop) [DecidablePred φ] :
    ((Z p).filter (fun z => Rc p (zpos z) ∧ Fc p (zpos z) ∧ φ (st p (zpos z)))).card =
      ∑ s ∈ States, if φ s then Fs p s else 0 := by
  rw [card_eq_sum_card_fiberwise (f := fun z => st p (zpos z)) (t := States)]
  · refine sum_congr rfl (fun s hs => ?_)
    split_ifs with h
    · unfold Fs; congr 1; ext z; simp only [mem_filter]
      constructor
      · rintro ⟨⟨hz, h1, h2, -⟩, rfl⟩; exact ⟨hz, h1, h2, rfl⟩
      · rintro ⟨hz, h1, h2, rfl⟩; exact ⟨⟨hz, h1, h2, h⟩, rfl⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro z hz rfl
      exact h (mem_filter.1 hz).2.2.2
  · intro z hz
    obtain ⟨-, h1, h2, -⟩ := mem_filter.1 hz
    exact st_mem _ h1 h2

open scoped Classical in
lemma Fs_succ (s' : ℤ × ℤ) :
    Fs (p + 1) s' = ∑ c ∈ range 3, ∑ s ∈ States,
      if (s.1 + c - 1 ≤ 1 ∧ s.2 - c + 1 ≤ 2 ∧
        (max (s.1 + c - 1) 0, max (s.2 - c + 1) 0) = s') then Fs p s else 0 := by
  unfold Fs
  rw [card_Z_succ]
  refine sum_congr rfl (fun c _ => ?_)
  have := card_by_state (p := p) (φ := fun s => s.1 + c - 1 ≤ 1 ∧ s.2 - c + 1 ≤ 2 ∧
    (max (s.1 + c - 1) 0, max (s.2 - c + 1) 0) = s')
  unfold Fs at this
  rw [← this]
  congr 1
  ext w
  simp only [mem_filter, Rc_snoc, Fc_snoc, st_snoc]
  tauto

lemma Fs_zero (s : ℤ × ℤ) : Fs 0 s = if s = (0, 0) then 1 else 0 := by
  unfold Fs
  have hZ : Z 0 = {Fin.elim0} := by
    ext z
    simp only [Z, Fintype.mem_piFinset, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ i => i.elim0⟩
  have hst : st 0 (zpos (Fin.elim0 : Fin 0 → ℕ)) = (0, 0) := by
    simp [st, wlo, whi]
  have hR : Rc 0 (zpos (Fin.elim0 : Fin 0 → ℕ)) := fun i j h1 h2 => by omega
  have hF : Fc 0 (zpos (Fin.elim0 : Fin 0 → ℕ)) := fun i j h1 h2 => by omega
  rw [hZ, filter_singleton]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (h1.2.2.symm.trans hst) h2
  · exact absurd ⟨hR, hF, h2 ▸ hst⟩ h1
  · simp

theorem Fs_closed (p : ℕ) :
    Fs p (0, 0) = 1 ∧ Fs p (1, 0) + 1 = 2 ^ p ∧ Fs p (0, 1) + 1 = 2 ^ p ∧
      2 * (Fs p (0, 2) + Fs p (1, 1)) + 2 ^ (p + 1) = p * 2 ^ p + 2 := by
  induction p with
  | zero => simp [Fs_zero]
  | succ p ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have e : ∀ s', Fs (p + 1) s' = _ := fun s' => Fs_succ (p := p) s'
    simp only [States, sum_range_succ, sum_range_zero, sum_insert, mem_insert, mem_singleton,
      Prod.mk.injEq, sum_singleton] at e
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e]; norm_num; omega
    · rw [e]; norm_num; rw [pow_succ]; omega
    · rw [e]; norm_num; rw [pow_succ]; omega
    · rw [e (0, 2), e (1, 1)]; norm_num
      zify at h3 h4 ⊢
      linear_combination 2 * h3 + 2 * h4

/-- Total number of words with rises `≤ 1` and falls `≤ 2`, doubled. -/
theorem card_RF (p : ℕ) :
    2 * ((Z p).filter (fun z => Rc p (zpos z) ∧ Fc p (zpos z))).card = (p + 2) * 2 ^ p := by
  classical
  have := card_by_state (p := p) (φ := fun _ => True)
  simp only [and_true, ite_true] at this
  rw [this]
  simp only [States, sum_insert, mem_insert, mem_singleton, Prod.mk.injEq, sum_singleton]
  norm_num
  obtain ⟨h1, h2, h3, h4⟩ := Fs_closed p
  zify at h1 h2 h3 h4 ⊢
  linear_combination 2 * h1 + 2 * h2 + 2 * h3 + h4

/-! ## Two-valued windows -/

/-- Words whose walk stays in `{lo, lo+1}` and ends at `e`. -/
noncomputable def Wc (p : ℕ) (lo e : ℤ) : ℕ :=
  ((Z p).filter (fun z => (∀ j ≤ p, lo ≤ P (zpos z) j ∧ P (zpos z) j ≤ lo + 1) ∧
    P (zpos z) p = e)).card

open scoped Classical in
lemma Wc_succ (lo e' : ℤ) (hlo1 : lo ≤ 0) (hlo2 : -1 ≤ lo) (he' : lo ≤ e' ∧ e' ≤ lo + 1) :
    Wc (p + 1) lo e' = Wc p lo lo + Wc p lo (lo + 1) := by
  unfold Wc
  rw [card_Z_succ]
  -- each previous end value `e` gives exactly one extension
  have key : ∀ e : ℤ, lo ≤ e → e ≤ lo + 1 →
      ∑ c ∈ range 3, ((Z p).filter (fun w => ((∀ j ≤ p, lo ≤ P (zpos w) j ∧ P (zpos w) j ≤ lo + 1)
        ∧ P (zpos w) p = e) ∧ P (zpos w) p + c - 1 = e')).card =
      ((Z p).filter (fun w => (∀ j ≤ p, lo ≤ P (zpos w) j ∧ P (zpos w) j ≤ lo + 1)
        ∧ P (zpos w) p = e)).card := by
    intro e h1 h2
    rw [sum_eq_single_of_mem ((e' - e + 1).toNat) (mem_range.2 (by omega))]
    · congr 1; ext w; simp only [mem_filter]
      constructor
      · rintro ⟨hz, h, -⟩; exact ⟨hz, h⟩
      · rintro ⟨hz, h⟩; refine ⟨hz, h, ?_⟩; rw [h.2]; omega
    · intro c _ hc
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro w - ⟨⟨-, h⟩, h'⟩
      apply hc; omega
  rw [← key lo le_rfl (by omega), ← key (lo + 1) (by omega) le_rfl, ← sum_add_distrib]
  refine sum_congr rfl (fun c _ => ?_)
  rw [← card_union_of_disjoint]
  · congr 1; ext w
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hz, hall, hend⟩
      have hp' := hall p (by omega)
      rw [P_snoc_le w c le_rfl] at hp'
      have hlast := hall (p + 1) le_rfl
      rw [P_snoc_last] at hlast hend
      have hall' : ∀ j ≤ p, lo ≤ P (zpos w) j ∧ P (zpos w) j ≤ lo + 1 := by
        intro j hj; have := hall j (by omega); rwa [P_snoc_le w c hj] at this
      rcases (show P (zpos w) p = lo ∨ P (zpos w) p = lo + 1 by omega) with h | h
      · left; exact ⟨hz, ⟨hall', h⟩, hend⟩
      · right; exact ⟨hz, ⟨hall', h⟩, hend⟩
    · rintro (⟨hz, ⟨hall, hend⟩, hc⟩ | ⟨hz, ⟨hall, hend⟩, hc⟩) <;>
      · refine ⟨hz, fun j hj => ?_, by rw [P_snoc_last]; omega⟩
        rcases eq_or_lt_of_le hj with rfl | hj'
        · rw [P_snoc_last]; omega
        · rw [P_snoc_le w c (by omega)]; exact hall j (by omega)
  · rw [disjoint_filter]
    intro w _ h1 h2
    omega

lemma Wc_sum (lo : ℤ) (hlo1 : lo ≤ 0) (hlo2 : -1 ≤ lo) (p : ℕ) :
    Wc p lo lo + Wc p lo (lo + 1) = 2 ^ p := by
  induction p with
  | zero =>
    unfold Wc
    have hZ : Z 0 = {Fin.elim0} := by
      ext z
      simp only [Z, Fintype.mem_piFinset, mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ i => i.elim0⟩
    rw [hZ, filter_singleton, filter_singleton]
    have h0 : P (zpos (Fin.elim0 : Fin 0 → ℕ)) 0 = 0 := rfl
    have hall : ∀ e : ℤ, ((∀ j ≤ 0, lo ≤ P (zpos (Fin.elim0 : Fin 0 → ℕ)) j ∧
        P (zpos (Fin.elim0 : Fin 0 → ℕ)) j ≤ lo + 1) ∧ P (zpos (Fin.elim0 : Fin 0 → ℕ)) 0 = e)
        ↔ e = 0 := by
      intro e; constructor
      · rintro ⟨-, h⟩; rw [h0] at h; omega
      · rintro rfl; refine ⟨fun j hj => ?_, h0⟩; rw [show j = 0 by omega, h0]; omega
    rw [if_congr (hall lo) rfl rfl, if_congr (hall (lo + 1)) rfl rfl]
    rcases (show lo = 0 ∨ lo = -1 by omega) with rfl | rfl <;> simp
  | succ p ih =>
    rw [Wc_succ lo lo hlo1 hlo2 ⟨le_rfl, by omega⟩, Wc_succ lo (lo + 1) hlo1 hlo2 ⟨by omega, le_rfl⟩,
      ih, pow_succ]
    ring

lemma Wc_eq (lo e : ℤ) (hlo1 : lo ≤ 0) (hlo2 : -1 ≤ lo) (he : lo ≤ e ∧ e ≤ lo + 1) (p : ℕ) :
    2 * Wc (p + 1) lo e = 2 ^ (p + 1) := by
  rw [Wc_succ lo e hlo1 hlo2 he, Wc_sum lo hlo1 hlo2 p, pow_succ]; ring

/-! ## The three counts used in Theorem E -/

/-- Tight words: `2 · #{Rc ∧ T = 1} = 2^p`. -/
theorem card_tight (p : ℕ) (hp : 1 ≤ p) :
    2 * ((Z p).filter (fun z => Rc p (zpos z) ∧ P (zpos z) p = 1)).card = 2 ^ p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [← Wc_eq 0 1 le_rfl (by norm_num) ⟨by norm_num, by norm_num⟩ q]
  unfold Wc
  congr 2
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨hz, hR, hT⟩
    refine ⟨hz, fun j hj => ?_, hT⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    rcases eq_or_lt_of_le hj with rfl | hj'
    · omega
    · have a := hR 0 j hj0 hj
      have b := hR j (q + 1) hj' le_rfl
      simp at a; omega
  · rintro ⟨hz, hall, hT⟩
    refine ⟨hz, fun i j hij hjp => ?_, hT⟩
    have a := hall i (by omega); have b := hall j hjp; omega

/-- The total over non-tight good words plus tight words. -/
theorem card_good_total (p : ℕ) :
    2 * (((Z p).filter (fun z => Rc p (zpos z) ∧ Fc p (zpos z) ∧ P (zpos z) p ≤ 0)).card +
      ((Z p).filter (fun z => Rc p (zpos z) ∧ P (zpos z) p = 1)).card) = (p + 2) * 2 ^ p := by
  rw [← card_RF p, ← card_union_of_disjoint]
  · congr 2
    ext z
    simp only [mem_filter, mem_union]
    constructor
    · rintro (⟨hz, hR, hF, -⟩ | ⟨hz, hR, hT⟩)
      · exact ⟨hz, hR, hF⟩
      · refine ⟨hz, hR, fun i j hij hjp => ?_⟩
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · omega
        have a := hR 0 i
        have b := hR i p
        have c := hR j p
        have d := hR 0 j
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · rcases eq_or_lt_of_le hjp with rfl | hj
          · simp; omega
          · have := c hj le_rfl; simp; omega
        · have := a hi (by omega)
          rcases eq_or_lt_of_le hjp with rfl | hj
          · simp at this; omega
          · have := c hj le_rfl; simp at *; omega
    · rintro ⟨hz, hR, hF⟩
      by_cases hT : P (zpos z) p ≤ 0
      · exact Or.inl ⟨hz, hR, hF, hT⟩
      · right; refine ⟨hz, hR, ?_⟩
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · simp at hT
        have := hR 0 p hp le_rfl; simp at this; omega
  · rw [disjoint_filter]; intro z _ h1 h2; omega

/-- `∑ (c_u + c_v - k)` over the non-tight good words equals the number of tight words. -/
theorem sum_ell (p : ℕ) (hp : 1 ≤ p) :
    2 * ∑ z ∈ (Z p).filter (fun z => Rc p (zpos z) ∧ Fc p (zpos z) ∧ P (zpos z) p ≤ 0),
      (C10 p (zpos z) + C01 p (zpos z) + P (zpos z) p) = (2 ^ p : ℤ) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hW := Wc_eq (-1) (-1) (by norm_num) le_rfl ⟨le_rfl, by norm_num⟩ q
  have hsum : ∑ z ∈ (Z (q + 1)).filter (fun z => Rc (q + 1) (zpos z) ∧ Fc (q + 1) (zpos z) ∧
      P (zpos z) (q + 1) ≤ 0), (C10 (q + 1) (zpos z) + C01 (q + 1) (zpos z) + P (zpos z) (q + 1)) =
      (Wc (q + 1) (-1) (-1) : ℤ) := by
    unfold Wc
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, sum_filter]
    refine sum_congr rfl (fun z hz => ?_)
    split_ifs with h1 h2 h2
    · obtain ⟨hR, hF, hT⟩ := h1
      obtain ⟨hall, hTe⟩ := h2
      unfold C10 C01
      rw [if_pos ⟨by omega, fun j hj => (hall j (by rw [mem_range] at hj; omega)).2⟩,
        if_pos ⟨by omega, fun j hj => by have := (hall j (by rw [mem_range] at hj; omega)).1; omega⟩]
      simp [hTe]
    · obtain ⟨hR, hF, hT⟩ := h1
      have hs := Csum hR hF hT
      have hF0 := hF 0 (q + 1) (by omega) le_rfl
      simp only [P_zero] at hF0
      have c1 := @C10_le_one (q + 1) (zpos z)
      have c2 := @C01_le_one (q + 1) (zpos z)
      try simp only [Nat.cast_zero]
      -- `ℓ ∈ {0,1}`, and `ℓ = 1` forces the window
      by_contra hne
      have hT1 : P (zpos z) (q + 1) = -1 := by
        rcases (show P (zpos z) (q + 1) = 0 ∨ P (zpos z) (q + 1) = -1 ∨
            P (zpos z) (q + 1) = -2 by omega) with h | h | h
        · exfalso; unfold C10 C01 at hne; rw [if_neg (by omega), if_neg (by omega)] at hne
          simp [h] at hne
        · exact h
        · exfalso; omega
      apply h2
      refine ⟨fun j hj => ⟨?_, ?_⟩, hT1⟩
      · have : C01 (q + 1) (zpos z) = 1 := by omega
        unfold C01 at this
        split_ifs at this with hc
        · have := hc.2 j (mem_range.2 (by omega)); omega
        · simp at this
      · have : C10 (q + 1) (zpos z) = 1 := by omega
        unfold C10 at this
        split_ifs at this with hc
        · exact hc.2 j (mem_range.2 (by omega))
        · simp at this
    · exfalso; apply h1
      obtain ⟨hall, hTe⟩ := h2
      refine ⟨fun i j hij hjp => ?_, fun i j hij hjp => ?_, by omega⟩
      · have a := hall i (by omega); have b := hall j hjp; omega
      · have a := hall i (by omega); have b := hall j hjp; omega
    · rfl
  rw [hsum]
  exact_mod_cast hW

end Drac
```

### `TheoremE.lean`

```lean
import FibreH
import WordCount

/-!
# Theorem E for good edges

If `uv` is an edge of `G` with `δ(G,uv) = 0`, gluing an `(p+2)`-cycle along `uv` multiplies the
number of draconian sequences by `(p+2) 2^{p-1}`:
`2 · |D(G ∪_{uv} C_{p+2})| = (p+2) · 2^p · |D(G)|`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset Ear

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V} {p : ℕ}

/-- The fibre of `D(G ∪ ear)` over `z`, as a set of `y`'s. -/
noncomputable def Yf (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (p : ℕ) (z : Fin p → ℕ) :
    Finset (V → ℕ) :=
  ((draconian (glue G u v p)).filter (fun x => x ∘ Sum.inr = z)).image (fun x => x ∘ Sum.inl)

lemma mem_Yf {z : Fin p → ℕ} {y : V → ℕ} :
    y ∈ Yf G u v p z ↔ Sum.elim y z ∈ draconian (glue G u v p) := by
  simp only [Yf, mem_image, mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
    have : x = Sum.elim (x ∘ Sum.inl) z := by
      funext i; cases i with
      | inl a => rfl
      | inr t => simp [← hz]
    rwa [← this]
  · intro h
    exact ⟨Sum.elim y z, ⟨h, rfl⟩, rfl⟩

lemma card_glue_eq_sum (huv : u ≠ v) (hp : 1 ≤ p) :
    (draconian (glue G u v p)).card = ∑ z ∈ Z p, (Yf G u v p z).card := by
  rw [card_eq_sum_card_fiberwise (f := fun x => x ∘ Sum.inr) (t := Z p)]
  · refine sum_congr rfl (fun z _ => ?_)
    rw [Yf, card_image_of_injOn]
    intro x₁ hx₁ x₂ hx₂ h
    simp only [coe_filter, Set.mem_setOf_eq] at hx₁ hx₂
    funext i
    cases i with
    | inl a => exact congrFun h a
    | inr t => exact (congrFun hx₁.2 t).trans (congrFun hx₂.2 t).symm
  · intro x hx
    rw [mem_coe] at hx
    have hx' : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) ∈ draconian (glue G u v p) := by
      have : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := by
        funext i; cases i <;> rfl
      rwa [this]
    have hR := Rc_of_mem G u v huv hp hx'
    rw [mem_coe, Z, Fintype.mem_piFinset]
    intro t
    have := hR t.val (t.val + 1) (by omega) (by have := t.isLt; omega)
    rw [P_succ, zpos_succ] at this
    simp only [Function.comp_apply] at this ⊢
    rw [mem_range]
    omega

/-- **Theorem E** (good edges). -/
theorem theoremE (huv : G.Adj u v) (hgood : Good G u v) (hp : 1 ≤ p) :
    2 * (draconian (glue G u v p)).card = (p + 2) * 2 ^ p * (draconian G).card := by
  have hne : u ≠ v := huv.ne
  set X := (draconian G).card
  set F := ((draconian G).image (proj u v)).card
  have hM := card_mminus (G := G) u v hne
  -- the value of each fibre
  have hfib : ∀ z ∈ Z p, ((Yf G u v p z).card : ℤ) =
      (if Rc p (zpos z) ∧ Fc p (zpos z) ∧ P (zpos z) p ≤ 0 then
        (X : ℤ) + (C10 p (zpos z) + C01 p (zpos z) + P (zpos z) p) * F else 0) +
      (if Rc p (zpos z) ∧ P (zpos z) p = 1 then (X : ℤ) - F else 0) := by
    intro z _
    by_cases hA : Rc p (zpos z) ∧ Fc p (zpos z) ∧ P (zpos z) p ≤ 0
    · obtain ⟨hR, hF, hT⟩ := hA
      rw [if_pos ⟨hR, hF, hT⟩, if_neg (by rintro ⟨-, h⟩; omega), add_zero]
      have hPs := P_eq_sum z
      have hzp : ∑ t, z t ≤ p := by omega
      set k := p - ∑ t, z t with hk
      have hTk : P (zpos z) p = -(k : ℤ) := by omega
      have c10a := @C10_nonneg p (zpos z)
      have c10b := @C10_le_one p (zpos z)
      have c01a := @C01_nonneg p (zpos z)
      have c01b := @C01_le_one p (zpos z)
      have hsum := Csum hR hF hT
      have hc10k : C10 p (zpos z) ≤ k := by
        unfold C10; split_ifs with h
        · omega
        · omega
      have hc01k : C01 p (zpos z) ≤ k := by
        unfold C01; split_ifs with h
        · omega
        · omega
      have heq : Yf G u v p z = mink G u v k (k - (C01 p (zpos z)).toNat) (C10 p (zpos z)).toNat := by
        ext y; rw [mem_Yf]; exact fibre_nontight G u v huv hp hR hF hT y
      rw [heq, card_mink u v hne (by omega) (by omega)]
      push_cast
      have e1 : ((C10 p (zpos z)).toNat : ℤ) = C10 p (zpos z) := Int.toNat_of_nonneg c10a
      have e2 : ((C01 p (zpos z)).toNat : ℤ) = C01 p (zpos z) := Int.toNat_of_nonneg c01a
      have e3 : (((C10 p (zpos z)).toNat - (k - (C01 p (zpos z)).toNat) : ℕ) : ℤ) =
          C10 p (zpos z) + C01 p (zpos z) - k := by omega
      rw [e3, hTk]
      ring
    · rw [if_neg hA]
      by_cases hB : Rc p (zpos z) ∧ P (zpos z) p = 1
      · rw [if_pos hB, zero_add]
        have heq : Yf G u v p z = mminus G u v := by
          ext y; rw [mem_Yf]; exact fibre_tight G u v huv hgood hp hB.1 hB.2 y
        rw [heq]
        omega
      · rw [if_neg hB, zero_add, Nat.cast_eq_zero, card_eq_zero, eq_empty_iff_forall_notMem]
        intro y hy
        rw [mem_Yf] at hy
        have hR := Rc_of_mem G u v hne hp hy
        have hF := Fc_of_mem G u v hne hp hy
        have h1 := T_le_one hp hR
        by_cases hT : P (zpos z) p ≤ 0
        · exact hA ⟨hR, hF, hT⟩
        · exact hB ⟨hR, by omega⟩
  have htot := card_good_total p
  have htight := card_tight p hp
  have hell := sum_ell p hp
  have hsumZ : ((draconian (glue G u v p)).card : ℤ) =
      ∑ z ∈ (Z p).filter (fun z => Rc p (zpos z) ∧ Fc p (zpos z) ∧ P (zpos z) p ≤ 0),
        ((X : ℤ) + (C10 p (zpos z) + C01 p (zpos z) + P (zpos z) p) * F) +
      ∑ z ∈ (Z p).filter (fun z => Rc p (zpos z) ∧ P (zpos z) p = 1), ((X : ℤ) - F) := by
    rw [card_glue_eq_sum hne hp, Nat.cast_sum, sum_congr rfl hfib, sum_add_distrib,
      sum_filter, sum_filter]
  rw [sum_add_distrib, sum_const, sum_const, ← sum_mul] at hsumZ
  zify
  rw [hsumZ]
  simp only [nsmul_eq_mul]
  have hell' := hell
  linear_combination (X : ℤ) * (by exact_mod_cast htot : (2 : ℤ) * (((Z p).filter
    (fun z => Rc p (zpos z) ∧ Fc p (zpos z) ∧ P (zpos z) p ≤ 0)).card +
    ((Z p).filter (fun z => Rc p (zpos z) ∧ P (zpos z) p = 1)).card) = (p + 2) * 2 ^ p)
    + (F : ℤ) * hell - (F : ℤ) * (by exact_mod_cast htight : (2 : ℤ) * ((Z p).filter
    (fun z => Rc p (zpos z) ∧ P (zpos z) p = 1)).card = 2 ^ p)

end Drac
```

### `Prop41.lean`

```lean
import FibreH
import Mathlib.Logic.Relation

/-!
# Outer edges are good (Proposition 4.1)

`G` is a graph whose vertices carry injective positions `pos`, such that no two edges cross
(`pos a < pos c < pos b < pos d` is impossible for edges `ab`, `cd`).  If `uv` is an edge,
`u` has the smallest position and `v` the second smallest, then `δ(G,uv) = 0`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No two edges cross with respect to the positions. -/
def NonCrossing (G : SimpleGraph V) (pos : V → ℕ) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj c d → ¬(pos a < pos c ∧ pos c < pos b ∧ pos b < pos d)

variable {pos : V → ℕ}

/-- (O2): a vertex strictly inside an edge's span has its neighbours in the closed span. -/
lemma O2 (hNC : NonCrossing G pos) {a b k l : V} (hab : G.Adj a b) (h1 : pos a < pos k)
    (h2 : pos k < pos b) (hkl : G.Adj k l) : pos a ≤ pos l ∧ pos l ≤ pos b := by
  constructor
  · by_contra h
    exact hNC l k a b hkl.symm hab ⟨by omega, h1, h2⟩
  · by_contra h
    exact hNC a b k l hab hkl ⟨h1, h2, by omega⟩

lemma sum_add_ind (y : V → ℕ) (w : V) (S : Finset V) :
    ∑ a ∈ S, (y + ind w 1) a = ∑ a ∈ S, y a + (if w ∈ S then 1 else 0) := by
  simp only [Pi.add_apply, sum_add_distrib, sum_ind]

/-- **Proposition 4.1.** -/
theorem good_of_outer (hpos : Function.Injective pos) (hNC : NonCrossing G pos) {u v : V}
    (huv : G.Adj u v) (hu : ∀ x, x ≠ u → pos u < pos x)
    (hv : ∀ x, x ≠ u → x ≠ v → pos v < pos x) : Good G u v := by
  have hne : u ≠ v := huv.ne
  intro y hyu hyv S hS huS hvS huN hvN
  rw [mem_draconian] at hyu hyv
  have hsy : ∑ a, y a + 1 = Fintype.card V - 1 := by
    have := hyu.1; rw [sum_add_ind] at this; simpa using this
  -- bound for sets avoiding `u`
  have bnd : ∀ T : Finset V, T.Nonempty → u ∉ T → ∑ a ∈ T, y a + 1 ≤ (cnbhd G T).card := by
    intro T hT huT
    have := hyu.2 T hT
    rw [sum_add_ind, if_neg huT] at this
    omega
  by_cases hsplit : ∃ S₁ ⊆ S, S₁.Nonempty ∧ (S \ S₁).Nonempty ∧
      Disjoint (cnbhd G S₁) (cnbhd G (S \ S₁))
  · -- Case 1: `S` splits
    obtain ⟨S₁, hsub, h1, h2, hdis⟩ := hsplit
    have e1 : S = S₁ ∪ (S \ S₁) := (union_sdiff_of_subset hsub).symm
    have b1 := bnd S₁ h1 (fun h => huS (hsub h))
    have b2 := bnd (S \ S₁) h2 (fun h => huS (mem_sdiff.1 h).1)
    have hs : ∑ a ∈ S, y a = ∑ a ∈ S₁, y a + ∑ a ∈ S \ S₁, y a := by
      conv_lhs => rw [e1]
      exact sum_union disjoint_sdiff
    have hc : (cnbhd G S).card = (cnbhd G S₁).card + (cnbhd G (S \ S₁)).card := by
      conv_lhs => rw [e1]
      rw [cnbhd_union, card_union_of_disjoint hdis]
    omega
  -- Case 2: `S` does not split
  push Not at hsplit
  set T := insert u S with hT
  set Rl : V → V → Prop := fun x x' => G.Adj x x' ∧ x ∉ T ∧ x' ∉ T with hRl
  set Z' := univ.filter (fun x => Relation.ReflTransGen Rl v x) with hZ'
  have hvT : v ∉ T := by simp [hT, hne.symm, hvS]
  have hvZ : v ∈ Z' := by simp [hZ', Relation.ReflTransGen.refl]
  have hZT : ∀ x ∈ Z', x ∉ T := by
    intro x hx
    simp only [hZ', mem_filter, mem_univ, true_and] at hx
    induction hx with
    | refl => exact hvT
    | tail _ h _ => exact h.2.2
  -- closure: a neighbour of a vertex of `Z'` is in `T` or in `Z'`
  have hZcl : ∀ x ∈ Z', ∀ x', G.Adj x x' → x' ∈ T ∨ x' ∈ Z' := by
    intro x hx x' hxx'
    by_cases h : x' ∈ T
    · exact Or.inl h
    · right
      simp only [hZ', mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.tail ⟨hxx', hZT x (by simp [hZ', hx]), h⟩
  set R := univ \ cnbhd G S with hR
  -- the claim: no vertex of `Z' ∩ R` is adjacent to `u`
  have claim : ∀ r ∈ Z', r ∈ R → ¬ G.Adj u r := by
    intro r hrZ hrR hur
    have hrN : r ∉ cnbhd G S := by simpa [hR] using hrR
    have hrS : r ∉ S := fun h => hrN (subset_cnbhd _ h)
    have hrv : r ≠ v := fun h => hrN (h ▸ hvN)
    have hru : r ≠ u := hur.ne.symm
    set ρ := pos r
    -- (A) neighbours of `u` in `S` lie beyond `r`
    have hA : ∀ a ∈ S, G.Adj u a → ρ < pos a := by
      intro a haS hua
      have hau : a ≠ u := hua.ne.symm
      have hav : a ≠ v := fun h => hvS (h ▸ haS)
      rcases lt_trichotomy (pos a) ρ with hlt | heq | hgt
      · exfalso
        -- every vertex reachable from `v` stays before `a`
        have inv : ∀ x ∈ Z', pos x < pos a := by
          intro x hx
          simp only [hZ', mem_filter, mem_univ, true_and] at hx
          induction hx with
          | refl => exact hv a hau hav
          | @tail b c _ hbc ih =>
            have hbu : b ≠ u := fun h => hbc.2.1 (by simp [hT, h])
            have := O2 hNC hua (hu b hbu) ih hbc.1
            have hca : c ≠ a := fun h => hbc.2.2 (by simp [hT, h, haS])
            have : pos c ≠ pos a := fun h => hca (hpos h)
            omega
        have := inv r hrZ
        omega
      · exact absurd (hpos heq) (fun h => hrS (h ▸ haS))
      · exact hgt
    set S₁ := S.filter (fun x => ρ < pos x) with hS₁
    -- some neighbour of `u` lies in `S`
    obtain ⟨a, haS, hua⟩ : ∃ a ∈ S, G.Adj a u := by
      rcases mem_cnbhd.1 huN with h | h
      · exact absurd h huS
      · exact h
    obtain ⟨b, hbS, hbv⟩ : ∃ b ∈ S, G.Adj b v := by
      rcases mem_cnbhd.1 hvN with h | h
      · exact absurd h hvS
      · exact h
    have hS1ne : S₁.Nonempty := ⟨a, by simp [hS₁, haS, hA a haS hua.symm]⟩
    have hbr : pos b < ρ := by
      have hbu : b ≠ u := fun h => huS (h ▸ hbS)
      have hbv' : b ≠ v := fun h => hvS (h ▸ hbS)
      by_contra hc
      have hle : pos r < pos b := by
        have : pos b ≠ ρ := fun h => hrS (hpos h ▸ hbS)
        omega
      -- (O3)
      have := O2 hNC hur (hu v hne.symm) (hv r hru hrv) hbv.symm
      omega
    have hS2ne : (S \ S₁).Nonempty := ⟨b, by simp [hS₁, hbS]; omega⟩
    have hnd := hsplit S₁ (filter_subset _ _) hS1ne hS2ne
    rw [not_disjoint_iff] at hnd
    obtain ⟨x, hx1, hx2⟩ := hnd
    -- positional consequences
    obtain ⟨s, hs, hsx⟩ : ∃ s ∈ S₁, x = s ∨ G.Adj s x := by
      rcases mem_cnbhd.1 hx1 with h | ⟨s, hs, h⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨s, hs, Or.inr h⟩
    obtain ⟨s', hs', hsx'⟩ : ∃ s' ∈ S \ S₁, x = s' ∨ G.Adj s' x := by
      rcases mem_cnbhd.1 hx2 with h | ⟨s, hs, h⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨s, hs, Or.inr h⟩
    simp only [hS₁, mem_filter, mem_sdiff, not_and, not_lt] at hs hs'
    have hs'S := hs'.1
    have hs'r : pos s' < ρ := by
      have := hs'.2 hs'S
      have : pos s' ≠ ρ := fun h => hrS (hpos h ▸ hs'S)
      omega
    have hs'u : s' ≠ u := fun h => huS (h ▸ hs'S)
    have hxS : x ∈ cnbhd G S := cnbhd_mono (filter_subset _ _) hx1
    have hxr : x ≠ r := fun h => hrN (h ▸ hxS)
    -- side of `s'`: `pos x ≤ ρ`
    have hx_le : pos x ≤ ρ := by
      rcases hsx' with rfl | h
      · omega
      · exact (O2 hNC hur (hu s' hs'u) hs'r h).2
    -- side of `s`: `x = u` or `pos x ≥ ρ`
    have hx_ge : x = u ∨ ρ ≤ pos x := by
      rcases hsx with rfl | h
      · right; omega
      · by_cases hxu : x = u
        · exact Or.inl hxu
        · right
          by_contra hc
          have := O2 hNC hur (hu x hxu) (by omega) h.symm
          omega
    rcases hx_ge with rfl | hge
    · -- `u ∈ N[s']`, so `s'` is a neighbour of `u` in `S`, hence beyond `r`
      rcases hsx' with h | h
      · exact hs'u h.symm
      · have := hA s' hs'S h.symm; omega
    · exact hxr (hpos (by omega))
  -- conclude with the component `Z'`
  have hZS : Disjoint S Z' := by
    rw [disjoint_left]; intro x hxS hxZ; exact hZT x hxZ (by simp [hT, hxS])
  have huZ : u ∉ Z' := fun h => hZT u h (by simp [hT])
  set X := S ∪ Z'
  -- (i) the upper bound on `X` from `y + e_v`
  have hX : ∑ a ∈ X, y a + 2 ≤ (cnbhd G X).card := by
    have := hyv.2 X ⟨v, mem_union_right _ hvZ⟩
    rw [sum_add_ind, if_pos (mem_union_right _ hvZ)] at this
    omega
  -- (ii) `N[X] ⊆ N[S] ∪ (Z' ∩ R)`
  have hNX : cnbhd G X ⊆ cnbhd G S ∪ (Z' ∩ R) := by
    intro w hw
    rw [cnbhd_union, mem_union] at hw
    rcases hw with hw | hw
    · exact mem_union_left _ hw
    · by_cases hwN : w ∈ cnbhd G S
      · exact mem_union_left _ hwN
      · apply mem_union_right
        have hwR : w ∈ R := by simp [hR, hwN]
        rcases mem_cnbhd.1 hw with hwZ | ⟨z, hz, hzw⟩
        · exact mem_inter.2 ⟨hwZ, hwR⟩
        · rcases hZcl z hz w hzw with hwT | hwZ
          · exfalso
            rcases mem_insert.1 hwT with rfl | hwS
            · exact hwN huN
            · exact hwN (subset_cnbhd _ hwS)
          · exact mem_inter.2 ⟨hwZ, hwR⟩
  -- (iii) the lower bound on `Z'` from `y + e_u` applied to the complement
  have hZlow : (Z' ∩ R).card ≤ ∑ a ∈ Z', y a := by
    set W := univ \ Z'
    have hWne : W.Nonempty := ⟨u, by simp [W, huZ]⟩
    have huW : u ∈ W := by simp [W, huZ]
    have h1 := hyu.2 W hWne
    rw [sum_add_ind, if_pos huW] at h1
    have hNW : cnbhd G W ⊆ univ \ (Z' ∩ R) := by
      intro w hw
      simp only [mem_sdiff, mem_univ, true_and, mem_inter]
      rintro ⟨hwZ, hwR⟩
      rcases mem_cnbhd.1 hw with hwW | ⟨w', hw'W, hw'w⟩
      · simp [W, hwZ] at hwW
      · -- the neighbour `w'` of `w` is outside `Z'`
        have hw'Z : w' ∉ Z' := by simpa [W] using hw'W
        rcases hZcl w hwZ w' hw'w.symm with hT' | hZ''
        · rcases mem_insert.1 hT' with rfl | hw'S
          · exact claim w hwZ hwR hw'w
          · have hwN : w ∈ cnbhd G S := mem_cnbhd.2 (Or.inr ⟨w', hw'S, hw'w⟩)
            simp [hR, hwN] at hwR
        · exact hw'Z hZ''
    have hc := card_le_card hNW
    rw [card_sdiff, card_univ, inter_univ] at hc
    have hsplitsum : ∑ a ∈ W, y a + ∑ a ∈ Z', y a = ∑ a, y a := by
      rw [← sum_union disjoint_sdiff_self_left]
      congr 1; ext; simp [W]
    have hZcard : (Z' ∩ R).card ≤ Fintype.card V := card_le_univ _
    omega
  have hsumX : ∑ a ∈ X, y a = ∑ a ∈ S, y a + ∑ a ∈ Z', y a := sum_union hZS
  have hcX : (cnbhd G X).card ≤ (cnbhd G S).card + (Z' ∩ R).card :=
    (card_le_card hNX).trans (card_union_le _ _)
  omega

end Drac
```

### `Statement.lean`

```lean
import Drac

/-!
# The statement (MathDB 347302, Davis–Chen Conjecture 36, block form)

* `Drac.draconian G`: the D(G)-draconian sequences (source, Definition 1 rephrased).
* `Dissection n`: a polygon on the vertices `0, …, n-1` (outer cycle `i ~ i+1`, `0 ~ n-1`)
  together with a set of pairwise non-crossing chords.  These are exactly the 2-connected
  outerplane graphs with a fixed outerplane embedding.
* `Drac.faces G`: the vertex sets inducing a cycle (at least three vertices, every vertex has
  exactly two neighbours inside, and the induced subgraph is connected).  For a dissection
  these are the bounded faces.
* `Dissection.ewdDeg D F`: the degree of `v_F` in the extended weak dual `B^(**)`, computed
  literally: the number of other bounded faces sharing an edge with `F`, plus the number of
  edges of `F` on the outer face.
* `Dissection.S D = ∑_F (deg_{B^(**)}(v_F) - 3)`.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Drac

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `A` induces a cycle in `G`: `|A| ≥ 3`, each vertex of `A` has exactly two neighbours in
`A`, and no nonempty proper subset of `A` is closed under taking neighbours inside `A`. -/
def IsFace (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Prop :=
  3 ≤ A.card ∧ (∀ x ∈ A, (A.filter (G.Adj x)).card = 2) ∧
    ∀ B ∈ A.powerset, B.Nonempty → (∀ x ∈ B, ∀ y ∈ A, G.Adj x y → y ∈ B) → B = A

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidablePred (IsFace G) := by
  intro A; unfold IsFace; infer_instance

/-- The bounded faces: vertex sets inducing a cycle. -/
def faces (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) := univ.filter (IsFace G)

end Drac

/-- A polygon dissection on the vertex set `Fin n`: chords `(i, j)` with `i + 2 ≤ j`, not the
outer edge `(0, n-1)`, pairwise non-crossing. -/
structure Dissection (n : ℕ) where
  chords : Finset (Fin n × Fin n)
  isChord : ∀ c ∈ chords, c.1.val + 2 ≤ c.2.val ∧ ¬(c.1.val = 0 ∧ c.2.val = n - 1)
  noncross : ∀ c ∈ chords, ∀ d ∈ chords, ¬(c.1 < d.1 ∧ d.1 < c.2 ∧ c.2 < d.2)

namespace Dissection

variable {n : ℕ}

/-- Adjacency along the outer cycle `0 — 1 — ⋯ — (n-1) — 0`. -/
def outerAdj (n : ℕ) (i j : Fin n) : Prop :=
  j.val = i.val + 1 ∨ i.val = j.val + 1 ∨ (i.val = 0 ∧ j.val = n - 1) ∨ (j.val = 0 ∧ i.val = n - 1)

instance (n : ℕ) : DecidableRel (outerAdj n) := fun i j => by unfold outerAdj; infer_instance

/-- The graph of the dissection: outer cycle plus chords. -/
def graph (D : Dissection n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (outerAdj n i j ∨ (i, j) ∈ D.chords ∨ (j, i) ∈ D.chords)
  symm := ⟨fun i j h => ⟨h.1.symm, by unfold outerAdj at h ⊢; tauto⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance (D : Dissection n) : DecidableRel D.graph.Adj := fun i j => by
  unfold graph; infer_instance

/-- The edges of the outer cycle, as pairs `(i, j)` with `i < j`. -/
def outerEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter (fun e => e.1 < e.2 ∧ (e.2.val = e.1.val + 1 ∨ (e.1.val = 0 ∧ e.2.val = n - 1)))

/-- Degree of `v_F` in the extended weak dual: other bounded faces sharing an edge with `F`,
plus edges of `F` on the outer face. -/
def ewdDeg (D : Dissection n) (F : Finset (Fin n)) : ℕ :=
  ((Drac.faces D.graph).filter (fun F' => F' ≠ F ∧
      ∃ x ∈ F, ∃ y ∈ F, D.graph.Adj x y ∧ x ∈ F' ∧ y ∈ F')).card +
    ((outerEdges n).filter (fun e => e.1 ∈ F ∧ e.2 ∈ F)).card

/-- `S(B) = ∑_{F} (deg_{B^(**)}(v_F) - 3)`. -/
def S (D : Dissection n) : ℤ := ∑ F ∈ Drac.faces D.graph, ((ewdDeg D F : ℤ) - 3)

end Dissection

/-- **Conjecture 36, block form** (the source's Eq. (9) for one 2-connected outerplane block,
in the draconian form `NVol(∇^PQ_B) = |D(B)|` of the source's Theorem 8). -/
def Conj36Block : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ D : Dissection n,
    (Drac.draconian D.graph).card =
      2 ^ (1 + D.S).toNat * ∏ F ∈ Drac.faces D.graph, D.ewdDeg F
```

### `DissA.lean`

```lean
import Prop41
import TheoremE
import Mathlib.Data.Fintype.EquivFin

/-!
# Polygon dissections given by positions; the minimal ear

A *position dissection* is a graph on a finite vertex set with injective positions such that
no two edges cross, positionally consecutive vertices are adjacent, and the first and last
vertices are adjacent (the outer cycle).  We find an edge `ab` of minimal span with a vertex
strictly inside, show that the vertices inside have degree two, and relabel `G` as
`G' ∪_{ab} ear` where `G'` is induced on the remaining vertices.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Position dissections. -/
structure PD (G : SimpleGraph V) (pos : V → ℕ) : Prop where
  inj : Function.Injective pos
  nc : NonCrossing G pos
  cons : ∀ x y, pos x < pos y → (∀ z, ¬(pos x < pos z ∧ pos z < pos y)) → G.Adj x y
  ends : ∀ x y, x ≠ y → (∀ z, pos x ≤ pos z ∧ pos z ≤ pos y) → G.Adj x y

/-- Vertices strictly between `a` and `b`. -/
noncomputable def btw (pos : V → ℕ) (a b : V) : Finset V :=
  univ.filter (fun z => pos a < pos z ∧ pos z < pos b)

/-- A minimal ear: an edge `ab` with something strictly inside, all of whose inner vertices
are adjacent only to positionally consecutive vertices. -/
structure MinEar (G : SimpleGraph V) (pos : V → ℕ) (a b : V) : Prop where
  adj : G.Adj a b
  lt : pos a < pos b
  ne : (btw pos a b).Nonempty
  inner : ∀ z k, z ∈ btw pos a b → G.Adj z k →
    pos a ≤ pos k ∧ pos k ≤ pos b ∧ ∀ w, ¬(min (pos z) (pos k) < pos w ∧ pos w < max (pos z) (pos k))

variable {G : SimpleGraph V} {pos : V → ℕ}

theorem exists_minEar (hG : PD G pos) (h3 : 3 ≤ Fintype.card V) : ∃ a b, MinEar G pos a b := by
  -- candidate edges
  set E := (univ : Finset (V × V)).filter
    (fun q => G.Adj q.1 q.2 ∧ pos q.1 < pos q.2 ∧ (btw pos q.1 q.2).Nonempty) with hE
  have hEne : E.Nonempty := by
    have hV : (univ : Finset V).Nonempty := by
      rw [← card_pos, card_univ]; omega
    obtain ⟨m, -, hm⟩ := exists_min_image univ pos hV
    obtain ⟨M, -, hM⟩ := exists_max_image univ pos hV
    obtain ⟨c, hcm, hcM⟩ : ∃ c, c ≠ m ∧ c ≠ M := by
      by_contra h
      push Not at h
      have : (univ : Finset V) ⊆ {m, M} := fun x _ => by
        by_cases hx : x = m
        · simp [hx]
        · simp [h x hx]
      have := card_le_card this
      rw [card_univ] at this
      have := card_le_two (a := m) (b := M)
      omega
    have hmc : pos m < pos c := lt_of_le_of_ne (hm c (mem_univ _)) (fun h => hcm (hG.inj h).symm)
    have hcM' : pos c < pos M := lt_of_le_of_ne (hM c (mem_univ _)) (fun h => hcM (hG.inj h))
    refine ⟨(m, M), ?_⟩
    simp only [hE, mem_filter, mem_univ, true_and]
    refine ⟨hG.ends m M (fun h => by subst h; omega) (fun z => ⟨hm z (mem_univ _), hM z (mem_univ _)⟩),
      by omega, ⟨c, by simp [btw]; omega⟩⟩
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := exists_min_image E (fun q => (btw pos q.1 q.2).card) hEne
  simp only [hE, mem_filter, mem_univ, true_and] at hab
  obtain ⟨hadj, hlt, hne⟩ := hab
  refine ⟨a, b, hadj, hlt, hne, fun z k hz hzk => ?_⟩
  simp only [btw, mem_filter, mem_univ, true_and] at hz
  have ho := O2 hG.nc hadj hz.1 hz.2 hzk
  refine ⟨ho.1, ho.2, fun w hw => ?_⟩
  -- otherwise `zk` (oriented) would be a candidate with a smaller span
  set lo := if pos z < pos k then z else k with hlo
  set hi := if pos z < pos k then k else z with hhi
  have hzk' : pos z ≠ pos k := fun h => G.irrefl (by rwa [hG.inj h] at hzk)
  have hlohi : pos lo = min (pos z) (pos k) ∧ pos hi = max (pos z) (pos k) := by
    simp only [hlo, hhi]; split_ifs <;> constructor <;> omega
  have hadj' : G.Adj lo hi := by
    simp only [hlo, hhi]; split_ifs
    · exact hzk
    · exact hzk.symm
  have hcand : (lo, hi) ∈ E := by
    simp only [hE, mem_filter, mem_univ, true_and]
    exact ⟨hadj', by omega, ⟨w, by simp [btw]; omega⟩⟩
  have hle := hmin _ hcand
  simp only at hle
  have hsub : btw pos lo hi ⊆ (btw pos a b).erase z := by
    intro x hx
    simp only [btw, mem_filter, mem_univ, true_and, mem_erase] at hx ⊢
    refine ⟨fun h => ?_, by omega, by omega⟩
    subst h
    have : pos x = pos lo ∨ pos x = pos hi := by omega
    omega
  have := card_le_card hsub
  rw [card_erase_of_mem (by simp [btw]; omega)] at this
  have : 0 < (btw pos a b).card := card_pos.2 hne
  omega

/-! ## Rotation preserves non-crossing -/

/-- Rotate positions so that `t` becomes `0` (`M` exceeds all positions). -/
def rot (t M n : ℕ) : ℕ := if t ≤ n then n - t else n + M

theorem nc_rot (hnc : NonCrossing G pos) (t M : ℕ) (hM : ∀ x, pos x < M) :
    NonCrossing G (fun x => rot t M (pos x)) := by
  intro a b c d hab hcd h
  have ha := hM a; have hb := hM b; have hc := hM c; have hd := hM d
  have i1 := hnc a b c d hab hcd
  have i2 := hnc c d a b hcd hab
  have i3 := hnc b a d c hab.symm hcd.symm
  have i4 := hnc d c b a hcd.symm hab.symm
  have i5 := hnc a b d c hab hcd.symm
  have i6 := hnc b a c d hab.symm hcd
  have i7 := hnc c d b a hcd hab.symm
  have i8 := hnc d c a b hcd.symm hab
  simp only [rot] at h
  split_ifs at h <;> omega

end Drac
```

### `DissB.lean`

```lean
import DissA

/-!
# Removing a minimal ear

For a minimal ear `ab` of a position dissection `G`, with inner vertices `I`, the graph `G` is
isomorphic to `G' ∪_{ab} C_{|I|+2}` where `G'` is induced on `V ∖ I`; `G'` is again a position
dissection and `ab` is an outer edge of `G'`, so Theorem E applies.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {pos : V → ℕ}

/-- The graph induced on the complement of `I`. -/
def subG (G : SimpleGraph V) (I : Finset V) : SimpleGraph {x // x ∉ I} where
  Adj x y := G.Adj x.1 y.1
  symm := ⟨fun x y h => G.adj_symm h⟩
  loopless := ⟨fun x h => G.irrefl h⟩

@[simp] lemma subG_adj {I : Finset V} {x y : {x // x ∉ I}} : (subG G I).Adj x y ↔ G.Adj x.1 y.1 :=
  Iff.rfl

lemma a_notMem {a b : V} : a ∉ btw pos a b := by simp [btw]
lemma b_notMem {a b : V} : b ∉ btw pos a b := by simp [btw]

/-- rank of an inner vertex. -/
noncomputable def rk (pos : V → ℕ) (I : Finset V) (z : V) : ℕ := (I.filter (fun w => pos w < pos z)).card

lemma mem_btw {x y z : V} : z ∈ btw pos x y ↔ pos x < pos z ∧ pos z < pos y := by simp [btw]

lemma rk_lt {I : Finset V} {z : V} (hz : z ∈ I) : rk pos I z < I.card := by
  apply card_lt_card
  refine ⟨filter_subset _ _, fun h => ?_⟩
  have := h hz
  simp at this

/-- The relabelling map `V → V' ⊕ Fin p`. -/
noncomputable def relab (pos : V → ℕ) (I : Finset V) (x : V) : {x // x ∉ I} ⊕ Fin I.card :=
  if h : x ∈ I then Sum.inr ⟨rk pos I x, rk_lt h⟩ else Sum.inl ⟨x, h⟩

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

lemma rk_succ {z z' : V} (hz : z ∈ btw pos a b) (hz' : z' ∈ btw pos a b) (hlt : pos z < pos z') :
    rk pos (btw pos a b) z' = rk pos (btw pos a b) z + (btw pos z z').card + 1 := by
  unfold rk
  have e : (btw pos a b).filter (fun w => pos w < pos z') =
      ((btw pos a b).filter (fun w => pos w < pos z)) ∪ (btw pos z z' ∪ {z}) := by
    ext w
    rw [mem_btw] at hz hz'
    simp only [mem_filter, mem_union, mem_btw, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy (pos w) (pos z) with h | h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr (Or.inr (hG.inj h))
      · exact Or.inr (Or.inl ⟨h, h2⟩)
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl)
      · exact ⟨h1, by omega⟩
      · exact ⟨⟨by omega, by omega⟩, h2⟩
      · exact ⟨hz, hlt⟩
  rw [e, card_union_of_disjoint, card_union_of_disjoint, card_singleton]
  · ring
  · rw [disjoint_left]; intro w h1 h2
    rw [mem_btw] at h1; rw [mem_singleton] at h2; subst h2; omega
  · rw [disjoint_left]; intro w h1 h2
    rw [mem_filter] at h1; rw [mem_union, mem_btw, mem_singleton] at h2
    rcases h2 with h2 | rfl
    · omega
    · omega

lemma rk_zero {z : V} (hz : z ∈ btw pos a b) :
    rk pos (btw pos a b) z = (btw pos a z).card := by
  unfold rk
  congr 1
  ext w
  rw [mem_btw] at hz
  simp only [mem_filter, mem_btw]
  omega

lemma rk_top {z : V} (hz : z ∈ btw pos a b) :
    rk pos (btw pos a b) z + 1 + (btw pos z b).card = (btw pos a b).card := by
  unfold rk
  have e : btw pos a b = ((btw pos a b).filter (fun w => pos w < pos z)) ∪ ({z} ∪ btw pos z b) := by
    ext w
    have hz' := mem_btw.1 hz
    simp only [mem_filter, mem_union, mem_btw, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy (pos w) (pos z) with h | h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr (Or.inl (hG.inj h))
      · exact Or.inr (Or.inr ⟨h, h2⟩)
    · rintro (⟨⟨h1, h2⟩, -⟩ | rfl | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact hz'
      · exact ⟨by omega, h2⟩
  conv_rhs => rw [e]
  rw [card_union_of_disjoint, card_union_of_disjoint, card_singleton]
  · ring
  · rw [disjoint_left]; intro w h1 h2; simp only [mem_singleton, mem_btw] at h1 h2; subst h1; omega
  · rw [disjoint_left]; intro w h1 h2; simp only [mem_filter, mem_union, mem_btw,
      mem_singleton] at h1 h2; rcases h2 with rfl | h2 <;> omega

/-- consecutive positions -/
lemma adj_of_empty {x y : V} (hlt : pos x < pos y) (h : btw pos x y = ∅) : G.Adj x y :=
  hG.cons x y hlt (fun w hw => by
    have : w ∈ btw pos x y := mem_btw.2 hw
    rw [h] at this; simp at this)

lemma inner_adj {z k : V} (hz : z ∈ btw pos a b) (hzk : G.Adj z k) :
    pos a ≤ pos k ∧ pos k ≤ pos b ∧
      btw pos (if pos z < pos k then z else k) (if pos z < pos k then k else z) = ∅ := by
  obtain ⟨h1, h2, h3⟩ := he.inner z k hz hzk
  refine ⟨h1, h2, ?_⟩
  rw [eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_btw] at hw
  apply h3 w
  split_ifs at hw with h
  · constructor <;> omega
  · constructor <;> omega

end

end Drac
```

### `DissC.lean`

```lean
import DissB

/-!
# The ear step: `2 |D(G)| = (p+2) 2^p |D(G')|`
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {pos : V → ℕ}

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

lemma relab_inj : Function.Injective (relab pos (btw pos a b)) := by
  intro x y h
  unfold relab at h
  by_cases hx : x ∈ btw pos a b <;> by_cases hy : y ∈ btw pos a b <;>
    simp only [hx, hy, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      Subtype.mk.injEq, Fin.mk.injEq] at h
  · rcases lt_trichotomy (pos x) (pos y) with hl | hl | hl
    · have := rk_succ hG he hx hy hl; omega
    · exact hG.inj hl
    · have := rk_succ hG he hy hx hl; omega
  · exact h

lemma card_compl_btw :
    Fintype.card {x // x ∉ btw pos a b} + (btw pos a b).card = Fintype.card V := by
  rw [Fintype.card_subtype, filter_not, card_sdiff, filter_mem_eq_inter, univ_inter, card_univ]
  · have := card_le_univ (btw pos a b)
    rw [inter_univ]
    omega

/-- The relabelling equivalence. -/
noncomputable def relabE : V ≃ {x // x ∉ btw pos a b} ⊕ Fin (btw pos a b).card :=
  Equiv.ofBijective (relab pos (btw pos a b))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨relab_inj hG he, by
      rw [Fintype.card_sum, Fintype.card_fin, card_compl_btw hG he]⟩)

lemma mixed_adj {x y : V} (hx : x ∉ btw pos a b) (hy : y ∈ btw pos a b) :
    ((x = a ∧ rk pos (btw pos a b) y = 0) ∨
      (x = b ∧ rk pos (btw pos a b) y + 1 = (btw pos a b).card)) ↔ G.Adj x y := by
  have hy' := mem_btw.1 hy
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · rw [rk_zero hG he hy, card_eq_zero] at h
      exact adj_of_empty hG he hy'.1 h
    · have := rk_top hG he hy
      have h0 : (btw pos y x).card = 0 := by omega
      rw [card_eq_zero] at h0
      exact (adj_of_empty hG he hy'.2 h0).symm
  · intro hxy
    obtain ⟨h1, h2, h3⟩ := inner_adj hG he hy hxy.symm
    have hxI : ¬(pos a < pos x ∧ pos x < pos b) := fun h => hx (mem_btw.2 h)
    rcases (show pos x = pos a ∨ pos x = pos b by omega) with h | h
    · left
      have hxa := hG.inj h
      subst hxa
      refine ⟨rfl, ?_⟩
      rw [rk_zero hG he hy, card_eq_zero]
      simpa [show ¬ pos y < pos x by omega] using h3
    · right
      have hxb := hG.inj h
      subst hxb
      refine ⟨rfl, ?_⟩
      have := rk_top hG he hy
      have h0 : btw pos y x = ∅ := by simpa [show pos y < pos x by omega] using h3
      rw [h0, card_empty] at this
      omega

lemma relab_adj (x y : V) :
    (glue (subG G (btw pos a b)) ⟨a, a_notMem⟩ ⟨b, b_notMem⟩ (btw pos a b).card).Adj
      (relab pos (btw pos a b) x) (relab pos (btw pos a b) y) ↔ G.Adj x y := by
  unfold relab
  by_cases hx : x ∈ btw pos a b <;> by_cases hy : y ∈ btw pos a b <;>
    simp only [hx, hy, dite_true, dite_false]
  · -- both inner
    change rk pos (btw pos a b) x + 1 = rk pos (btw pos a b) y ∨
      rk pos (btw pos a b) y + 1 = rk pos (btw pos a b) x ↔ G.Adj x y
    constructor
    · intro h
      rcases lt_trichotomy (pos x) (pos y) with hl | hl | hl
      · have := rk_succ hG he hx hy hl
        have h0 : (btw pos x y).card = 0 := by omega
        rw [card_eq_zero] at h0
        exact adj_of_empty hG he hl h0
      · rw [hG.inj hl] at h; omega
      · have := rk_succ hG he hy hx hl
        have h0 : (btw pos y x).card = 0 := by omega
        rw [card_eq_zero] at h0
        exact (adj_of_empty hG he hl h0).symm
    · intro hxy
      obtain ⟨-, -, h3⟩ := inner_adj hG he hx hxy
      have hne : pos x ≠ pos y := fun h => G.irrefl (by rwa [hG.inj h] at hxy)
      rcases lt_or_gt_of_ne hne with hl | hl
      · left
        have := rk_succ hG he hx hy hl
        simp only [hl, ite_true] at h3
        rw [h3, card_empty] at this; omega
      · right
        have := rk_succ hG he hy hx hl
        simp only [show ¬ pos x < pos y by omega, ite_false] at h3
        rw [h3, card_empty] at this; omega
  · -- `x` inner, `y` outer
    change (⟨y, hy⟩ = (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∧ rk pos (btw pos a b) x = 0) ∨
      (⟨y, hy⟩ = (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∧
        rk pos (btw pos a b) x + 1 = (btw pos a b).card) ↔ G.Adj x y
    simp only [Subtype.mk.injEq]
    rw [G.adj_comm]
    exact mixed_adj hG he hy hx
  · change (⟨x, hx⟩ = (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∧ rk pos (btw pos a b) y = 0) ∨
      (⟨x, hx⟩ = (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∧
        rk pos (btw pos a b) y + 1 = (btw pos a b).card) ↔ G.Adj x y
    simp only [Subtype.mk.injEq]
    exact mixed_adj hG he hx hy
  · exact Iff.rfl

/-- `G'` is again a position dissection. -/
theorem PD_sub : PD (subG G (btw pos a b)) (fun x => pos x.1) := by
  refine ⟨fun x y h => Subtype.ext (hG.inj h), fun x y z w h1 h2 => hG.nc _ _ _ _ h1 h2, ?_, ?_⟩
  · intro x y hlt hnone
    by_cases h : ∃ w, pos x.1 < pos w ∧ pos w < pos y.1
    · obtain ⟨w, hw1, hw2⟩ := h
      have hwI : w ∈ btw pos a b := by
        by_contra hw; exact hnone ⟨w, hw⟩ ⟨hw1, hw2⟩
      have hw' := mem_btw.1 hwI
      have ha := hnone ⟨a, a_notMem⟩
      have hb := hnone ⟨b, b_notMem⟩
      simp only at ha hb
      have hx := x.2; have hy := y.2
      rw [mem_btw] at hx hy
      have hxa : x.1 = a := hG.inj (by omega)
      have hyb : y.1 = b := hG.inj (by omega)
      show G.Adj x.1 y.1
      rw [hxa, hyb]; exact he.adj
    · push Not at h
      exact hG.cons _ _ hlt (fun w hw => by have := h w hw.1; omega)
  · intro x y hxy hall
    have ha := hall ⟨a, a_notMem⟩
    have hb := hall ⟨b, b_notMem⟩
    simp only at ha hb
    exact hG.ends x.1 y.1 (fun h => hxy (Subtype.ext h)) (fun z => by
      by_cases hz : z ∈ btw pos a b
      · have := mem_btw.1 hz; constructor <;> omega
      · exact hall ⟨z, hz⟩)

/-- `ab` is a good edge of `G'` (Proposition 4.1 after rotating the positions). -/
theorem good_sub : Good (subG G (btw pos a b)) ⟨a, a_notMem⟩ ⟨b, b_notMem⟩ := by
  set M := univ.sup pos + 1
  have hM : ∀ x, pos x < M := fun x => Nat.lt_succ_of_le (le_sup (mem_univ x))
  have hPD := PD_sub hG he
  have hlt := he.lt
  refine good_of_outer (pos := fun x => rot (pos a) M (pos x.1)) ?_ ?_ he.adj ?_ ?_
  · intro x y h
    simp only [rot] at h
    have := hM x.1; have := hM y.1
    apply hPD.inj
    simp only
    split_ifs at h <;> omega
  · exact nc_rot hPD.nc (pos a) M (fun x => hM x.1)
  · intro x hx
    have hne : pos x.1 ≠ pos a := fun h => hx (Subtype.ext (hG.inj h))
    simp only [rot]
    split_ifs <;> omega
  · intro x hxa hxb
    have hne1 : pos x.1 ≠ pos a := fun h => hxa (Subtype.ext (hG.inj h))
    have hne2 : pos x.1 ≠ pos b := fun h => hxb (Subtype.ext (hG.inj h))
    have hxI : ¬(pos a < pos x.1 ∧ pos x.1 < pos b) := fun h => x.2 (mem_btw.2 h)
    have := hM b
    simp only [rot]
    split_ifs <;> omega

/-- **The ear step.** -/
theorem ear_step :
    2 * (draconian G).card =
      ((btw pos a b).card + 2) * 2 ^ (btw pos a b).card *
        (draconian (subG G (btw pos a b))).card := by
  rw [card_draconian_congr (glue (subG G (btw pos a b)) ⟨a, a_notMem⟩ ⟨b, b_notMem⟩
    (btw pos a b).card) (relabE hG he) (fun x y => by
      simp only [relabE, Equiv.ofBijective_apply]; exact relab_adj hG he x y)]
  exact theoremE (G := subG G (btw pos a b)) he.adj (good_sub hG he)
    (card_pos.2 he.ne)

lemma card_sub_lt : Fintype.card {x // x ∉ btw pos a b} < Fintype.card V := by
  have := card_compl_btw hG he
  have := card_pos.2 he.ne
  omega

lemma two_le_card_sub : 2 ≤ Fintype.card {x // x ∉ btw pos a b} := by
  rw [← card_univ]
  exact one_lt_card.2 ⟨⟨a, a_notMem⟩, mem_univ _, ⟨b, b_notMem⟩, mem_univ _,
    fun h => by
      have h' := congrArg Subtype.val h; simp only at h'
      have := he.lt; rw [h'] at this; exact lt_irrefl _ this⟩

end

end Drac
```

### `DissD.lean`

```lean
import DissC
import Statement

/-!
# Faces under removal of a minimal ear

`faces G = {F₀} ∪ faces G'` where `F₀ = {x : pos a ≤ pos x ≤ pos b}` and the faces of
`G'` are transported along the inclusion `V' ⊆ V`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {pos : V → ℕ}

/-- Positionally convex sets. -/
def Convex (pos : V → ℕ) (C : Finset V) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z, pos x ≤ pos z → pos z ≤ pos y → z ∈ C

/-- A nonempty subset of a convex set closed under passing to consecutive vertices is all. -/
lemma convex_closed (hinj : Function.Injective pos) {C B : Finset V} (hC : Convex pos C)
    (hBC : B ⊆ C) (hB : B.Nonempty)
    (hcl : ∀ x ∈ B, ∀ y ∈ C, btw pos (if pos x < pos y then x else y)
      (if pos x < pos y then y else x) = ∅ → y ∈ B) : B = C := by
  by_contra hne
  obtain ⟨y, hyC, hyB⟩ : ∃ y ∈ C, y ∉ B := by
    by_contra h; push Not at h; exact hne (Subset.antisymm hBC h)
  by_cases hlow : (B.filter (fun x => pos x < pos y)).Nonempty
  · obtain ⟨x, hx, hxmax⟩ := exists_max_image _ pos hlow
    rw [mem_filter] at hx
    set U := univ.filter (fun s => pos x < pos s ∧ pos s ≤ pos y)
    have hU : U.Nonempty := ⟨y, by simp [U]; omega⟩
    obtain ⟨s, hs, hsmin⟩ := exists_min_image U pos hU
    simp only [U, mem_filter, mem_univ, true_and] at hs
    have hsC : s ∈ C := hC x (hBC hx.1) y hyC s hs.1.le hs.2
    have hempty : btw pos x s = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      rw [mem_btw] at hw
      have := hsmin w (by simp [U]; omega)
      omega
    have hsB : s ∈ B := hcl x hx.1 s hsC (by simpa [hs.1] using hempty)
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · have := hxmax s (mem_filter.2 ⟨hsB, hlt⟩); omega
    · exact hyB (hinj heq ▸ hsB)
  · obtain ⟨x0, hx0⟩ := hB
    have hhigh : (B.filter (fun x => pos y < pos x)).Nonempty := by
      refine ⟨x0, mem_filter.2 ⟨hx0, ?_⟩⟩
      have h1 : ¬ pos x0 < pos y := fun h => hlow ⟨x0, mem_filter.2 ⟨hx0, h⟩⟩
      have h2 : pos x0 ≠ pos y := fun h => hyB (hinj h ▸ hx0)
      omega
    obtain ⟨x, hx, hxmin⟩ := exists_min_image _ pos hhigh
    rw [mem_filter] at hx
    set U := univ.filter (fun s => pos y ≤ pos s ∧ pos s < pos x)
    have hU : U.Nonempty := ⟨y, by simp [U]; omega⟩
    obtain ⟨s, hs, hsmax⟩ := exists_max_image U pos hU
    simp only [U, mem_filter, mem_univ, true_and] at hs
    have hsC : s ∈ C := hC y hyC x (hBC hx.1) s hs.1 hs.2.le
    have hempty : btw pos s x = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      rw [mem_btw] at hw
      have := hsmax w (by simp [U]; omega)
      omega
    have hsB : s ∈ B := hcl x hx.1 s hsC (by simpa [show ¬ pos x < pos s by omega] using hempty)
    rcases lt_or_eq_of_le hs.1 with hlt | heq
    · have := hxmin s (mem_filter.2 ⟨hsB, hlt⟩); omega
    · exact hyB (hinj heq.symm ▸ hsB)

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

/-- The new face `F₀`. -/
noncomputable def F0 (pos : V → ℕ) (a b : V) : Finset V :=
  univ.filter (fun x => pos a ≤ pos x ∧ pos x ≤ pos b)

omit hG he in
lemma mem_F0 {x : V} : x ∈ F0 pos a b ↔ pos a ≤ pos x ∧ pos x ≤ pos b := by simp [F0]

lemma F0_eq : F0 pos a b = insert a (insert b (btw pos a b)) := by
  have hlt := he.lt
  ext x
  simp only [mem_F0, mem_insert, mem_btw]
  constructor
  · intro h
    by_cases h1 : pos x = pos a
    · exact Or.inl (hG.inj h1)
    by_cases h2 : pos x = pos b
    · exact Or.inr (Or.inl (hG.inj h2))
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · rintro (rfl | rfl | h) <;> omega

lemma card_F0 : (F0 pos a b).card = (btw pos a b).card + 2 := by
  rw [F0_eq hG he, card_insert_of_notMem, card_insert_of_notMem b_notMem]
  simp only [mem_insert, not_or]
  exact ⟨fun h => by have := he.lt; rw [h] at this; omega, a_notMem⟩

/-- Consecutive successors and predecessors. -/
lemma exists_succ (x : V) (h : ∃ z, pos x < pos z) :
    ∃ s, pos x < pos s ∧ btw pos x s = ∅ := by
  have hU : (univ.filter (fun z => pos x < pos z)).Nonempty := by
    obtain ⟨z, hz⟩ := h; exact ⟨z, by simp [hz]⟩
  obtain ⟨s, hs, hmin⟩ := exists_min_image _ pos hU
  simp only [mem_filter, mem_univ, true_and] at hs
  refine ⟨s, hs, eq_empty_iff_forall_notMem.2 (fun w hw => ?_)⟩
  rw [mem_btw] at hw
  have := hmin w (by simp; omega)
  omega

lemma exists_pred (x : V) (h : ∃ z, pos z < pos x) :
    ∃ s, pos s < pos x ∧ btw pos s x = ∅ := by
  have hU : (univ.filter (fun z => pos z < pos x)).Nonempty := by
    obtain ⟨z, hz⟩ := h; exact ⟨z, by simp [hz]⟩
  obtain ⟨s, hs, hmax⟩ := exists_max_image _ pos hU
  simp only [mem_filter, mem_univ, true_and] at hs
  refine ⟨s, hs, eq_empty_iff_forall_notMem.2 (fun w hw => ?_)⟩
  rw [mem_btw] at hw
  have := hmax w (by simp; omega)
  omega

/-- Neighbours of an inner vertex are exactly the consecutive ones. -/
lemma inner_adj_iff {z y : V} (hz : z ∈ btw pos a b) :
    G.Adj z y ↔ (pos z < pos y ∧ btw pos z y = ∅) ∨ (pos y < pos z ∧ btw pos y z = ∅) := by
  constructor
  · intro h
    obtain ⟨-, -, h3⟩ := inner_adj hG he hz h
    have hne : pos z ≠ pos y := fun hh => G.irrefl (by rwa [hG.inj hh] at h)
    rcases lt_or_gt_of_ne hne with hl | hl
    · left; simp only [hl, ite_true] at h3; exact ⟨hl, h3⟩
    · right; simp only [show ¬ pos z < pos y by omega, ite_false] at h3; exact ⟨hl, h3⟩
  · rintro (⟨hl, h⟩ | ⟨hl, h⟩)
    · exact adj_of_empty hG he hl h
    · exact (adj_of_empty hG he hl h).symm

lemma consec_unique_up {x s s' : V} (h1 : pos x < pos s) (h2 : btw pos x s = ∅) (h1' : pos x < pos s')
    (h2' : btw pos x s' = ∅) : s = s' := by
  apply hG.inj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have : s ∈ btw pos x s' := mem_btw.2 ⟨h1, hl⟩
    rw [h2'] at this; simp at this
  · have : s' ∈ btw pos x s := mem_btw.2 ⟨h1', hl⟩
    rw [h2] at this; simp at this

lemma consec_unique_down {x s s' : V} (h1 : pos s < pos x) (h2 : btw pos s x = ∅) (h1' : pos s' < pos x)
    (h2' : btw pos s' x = ∅) : s = s' := by
  apply hG.inj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have : s' ∈ btw pos s x := mem_btw.2 ⟨hl, h1'⟩
    rw [h2] at this; simp at this
  · have : s ∈ btw pos s' x := mem_btw.2 ⟨hl, h1⟩
    rw [h2'] at this; simp at this

lemma succ_le_of {x s z : V} (hxs : pos x < pos s) (h : btw pos x s = ∅) (hz : pos x < pos z) :
    pos s ≤ pos z := by
  by_contra hc
  have : z ∈ btw pos x s := mem_btw.2 ⟨hz, by omega⟩
  rw [h] at this; simp at this

omit hG he in
lemma pred_ge_of (hinj : Function.Injective pos) {x s z : V} (hsx : pos s < pos x)
    (h : btw pos s x = ∅) (hz : pos z < pos x) : pos z ≤ pos s := by
  by_contra hc
  have : z ∈ btw pos s x := mem_btw.2 ⟨by omega, hz⟩
  rw [h] at this; simp at this

/-- Every neighbour of an inner vertex lies in `F₀`, and the inner vertex has exactly two
neighbours, its positional predecessor and successor. -/
lemma inner_nbrs {z : V} (hz : z ∈ btw pos a b) :
    ∃ q s, pos q < pos z ∧ pos z < pos s ∧ q ∈ F0 pos a b ∧ s ∈ F0 pos a b ∧
      ∀ y, G.Adj z y ↔ (y = q ∨ y = s) := by
  have hz' := mem_btw.1 hz
  obtain ⟨s, hs1, hs2⟩ := exists_succ hG he z ⟨b, hz'.2⟩
  obtain ⟨q, hq1, hq2⟩ := exists_pred hG he z ⟨a, hz'.1⟩
  have hsb := succ_le_of hG he hs1 hs2 hz'.2
  have hqa := pred_ge_of hG.inj hq1 hq2 hz'.1
  refine ⟨q, s, hq1, hs1, mem_F0.2 ⟨hqa, by omega⟩, mem_F0.2 ⟨by omega, hsb⟩, fun y => ?_⟩
  rw [inner_adj_iff hG he hz]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr (consec_unique_up hG he h1 h2 hs1 hs2)
    · exact Or.inl (consec_unique_down hG he h1 h2 hq1 hq2)
  · rintro (rfl | rfl)
    · exact Or.inr ⟨hq1, hq2⟩
    · exact Or.inl ⟨hs1, hs2⟩

/-- Neighbours of `a` inside `F₀`: `b` and the successor of `a`. -/
lemma a_nbrs : ∃ s, s ∈ btw pos a b ∧ btw pos a s = ∅ ∧ G.Adj a s ∧
    ∀ y ∈ F0 pos a b, G.Adj a y → (y = b ∨ y = s) := by
  obtain ⟨c, hc⟩ := he.ne
  have hc' := mem_btw.1 hc
  obtain ⟨s, hs1, hs2⟩ := exists_succ hG he a ⟨c, hc'.1⟩
  have hsc := succ_le_of hG he hs1 hs2 hc'.1
  have hsI : s ∈ btw pos a b := mem_btw.2 ⟨hs1, by omega⟩
  refine ⟨s, hsI, hs2, adj_of_empty hG he hs1 hs2, fun y hy hay => ?_⟩
  rw [F0_eq hG he, mem_insert, mem_insert] at hy
  rcases hy with rfl | rfl | hy
  · exact absurd hay G.irrefl
  · exact Or.inl rfl
  · right
    have hy' := mem_btw.1 hy
    rcases (inner_adj_iff hG he hy).1 hay.symm with h | h
    · omega
    · exact consec_unique_up hG he h.1 h.2 hs1 hs2

/-- Neighbours of `b` inside `F₀`: `a` and the predecessor of `b`. -/
lemma b_nbrs : ∃ q, q ∈ btw pos a b ∧ btw pos q b = ∅ ∧ G.Adj q b ∧
    ∀ y ∈ F0 pos a b, G.Adj b y → (y = a ∨ y = q) := by
  obtain ⟨c, hc⟩ := he.ne
  have hc' := mem_btw.1 hc
  obtain ⟨q, hq1, hq2⟩ := exists_pred hG he b ⟨c, hc'.2⟩
  have hqc := pred_ge_of hG.inj hq1 hq2 hc'.2
  have hqI : q ∈ btw pos a b := mem_btw.2 ⟨by omega, hq1⟩
  refine ⟨q, hqI, hq2, adj_of_empty hG he hq1 hq2, fun y hy hby => ?_⟩
  rw [F0_eq hG he, mem_insert, mem_insert] at hy
  rcases hy with rfl | rfl | hy
  · exact Or.inl rfl
  · exact absurd hby G.irrefl
  · right
    have hy' := mem_btw.1 hy
    rcases (inner_adj_iff hG he hy).1 hby.symm with h | h
    · exact consec_unique_down hG he h.1 h.2 hq1 hq2
    · omega

lemma convex_F0 : Convex pos (F0 pos a b) := by
  intro x hx y hy z h1 h2; rw [mem_F0] at hx hy ⊢; omega

lemma convex_btw : Convex pos (btw pos a b) := by
  intro x hx y hy z h1 h2; rw [mem_btw] at hx hy ⊢; omega

lemma closure_consec {B : Finset V} (hcl : ∀ x ∈ B, ∀ y ∈ F0 pos a b, G.Adj x y → y ∈ B) :
    ∀ x ∈ B, ∀ y ∈ F0 pos a b, btw pos (if pos x < pos y then x else y)
      (if pos x < pos y then y else x) = ∅ → x ≠ y → y ∈ B := by
  intro x hx y hy hemp hxy
  apply hcl x hx y hy
  have hne : pos x ≠ pos y := fun h => hxy (hG.inj h)
  rcases lt_or_gt_of_ne hne with hl | hl
  · simp only [hl, ite_true] at hemp; exact adj_of_empty hG he hl hemp
  · simp only [show ¬ pos x < pos y by omega, ite_false] at hemp
    exact (adj_of_empty hG he hl hemp).symm

/-- `F₀` is a face of `G`. -/
theorem isFace_F0 : IsFace G (F0 pos a b) := by
  refine ⟨by rw [card_F0 hG he]; have := card_pos.2 he.ne; omega, ?_, ?_⟩
  · intro x hx
    have hx' := mem_F0.1 hx
    rw [F0_eq hG he, mem_insert, mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · obtain ⟨s, hsI, -, has, hall⟩ := a_nbrs hG he
      have : (F0 pos x b).filter (G.Adj x) = {b, s} := by
        ext y
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hy, hxy⟩; exact hall y hy hxy
        · rintro (rfl | rfl)
          · exact ⟨mem_F0.2 ⟨he.lt.le, le_rfl⟩, he.adj⟩
          · have := mem_btw.1 hsI; exact ⟨mem_F0.2 ⟨by omega, by omega⟩, has⟩
      rw [this, card_insert_of_notMem (by simp; rintro rfl; exact b_notMem hsI), card_singleton]
    · obtain ⟨q, hqI, -, hqb, hall⟩ := b_nbrs hG he
      have : (F0 pos a x).filter (G.Adj x) = {a, q} := by
        ext y
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hy, hxy⟩; exact hall y hy hxy
        · rintro (rfl | rfl)
          · exact ⟨mem_F0.2 ⟨le_rfl, he.lt.le⟩, he.adj.symm⟩
          · have := mem_btw.1 hqI; exact ⟨mem_F0.2 ⟨by omega, by omega⟩, hqb.symm⟩
      rw [this, card_insert_of_notMem (by simp; rintro rfl; exact a_notMem hqI), card_singleton]
    · obtain ⟨q, s, hq, hs, hqF, hsF, hall⟩ := inner_nbrs hG he hx
      have : (F0 pos a b).filter (G.Adj x) = {q, s} := by
        ext y
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨-, hxy⟩; exact (hall y).1 hxy
        · rintro (rfl | rfl)
          · exact ⟨hqF, (hall _).2 (Or.inl rfl)⟩
          · exact ⟨hsF, (hall _).2 (Or.inr rfl)⟩
      rw [this, card_insert_of_notMem (by simp; rintro rfl; omega), card_singleton]
  · intro B hB hBne hcl
    rw [mem_powerset] at hB
    refine convex_closed hG.inj (convex_F0 hG he) hB hBne (fun x hx y hy hemp => ?_)
    by_cases hxy : x = y
    · exact hxy ▸ hx
    · exact closure_consec hG he hcl x hx y hy hemp hxy

/-- A face meeting the inner vertices is `F₀`. -/
theorem face_eq_F0 {A : Finset V} (hA : IsFace G A) (hmeet : (A ∩ btw pos a b).Nonempty) :
    A = F0 pos a b := by
  obtain ⟨hA3, hA2, hAc⟩ := hA
  -- neighbours of inner vertices of `A` lie in `A`
  have step1 : ∀ w ∈ A, w ∈ btw pos a b → ∀ y, G.Adj w y → y ∈ A := by
    intro w hwA hwI y hwy
    obtain ⟨q, s, hq, hs, -, -, hall⟩ := inner_nbrs hG he hwI
    have hsub : A.filter (G.Adj w) ⊆ {q, s} := by
      intro t ht
      rw [mem_filter] at ht
      rcases (hall t).1 ht.2 with rfl | rfl <;> simp
    have hcard : ({q, s} : Finset V).card = 2 := by
      rw [card_insert_of_notMem (by simp; rintro rfl; omega), card_singleton]
    have heq := eq_of_subset_of_card_le hsub (by rw [hcard, hA2 w hwA])
    have : y ∈ ({q, s} : Finset V) := by
      rcases (hall y).1 hwy with rfl | rfl <;> simp
    rw [← heq] at this
    exact (mem_filter.1 this).1
  -- all inner vertices are in `A`
  have hIA : btw pos a b ⊆ A := by
    have := convex_closed hG.inj (convex_btw hG he) (inter_subset_right (s₁ := A))
      hmeet (fun x hx y hy hemp => by
        rw [mem_inter] at hx ⊢
        refine ⟨?_, hy⟩
        by_cases hxy : x = y
        · exact hxy ▸ hx.1
        · apply step1 x hx.1 hx.2 y
          have hne : pos x ≠ pos y := fun h => hxy (hG.inj h)
          rcases lt_or_gt_of_ne hne with hl | hl
          · simp only [hl, ite_true] at hemp; exact adj_of_empty hG he hl hemp
          · simp only [show ¬ pos x < pos y by omega, ite_false] at hemp
            exact (adj_of_empty hG he hl hemp).symm)
    rw [← this]; exact inter_subset_left
  obtain ⟨s, hsI, -, has, halla⟩ := a_nbrs hG he
  obtain ⟨q, hqI, -, hqb, hallb⟩ := b_nbrs hG he
  have haA : a ∈ A := step1 s (hIA hsI) hsI a has.symm
  have hbA : b ∈ A := step1 q (hIA hqI) hqI b hqb
  have hF0A : F0 pos a b ⊆ A := by
    rw [F0_eq hG he]
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact haA
    rcases mem_insert.1 hx with rfl | hx
    · exact hbA
    · exact hIA hx
  -- `F₀` is closed under neighbours inside `A`
  symm
  apply hAc (F0 pos a b) (mem_powerset.2 hF0A) ⟨a, mem_F0.2 ⟨le_rfl, he.lt.le⟩⟩
  intro x hx y hyA hxy
  have hx' := hx
  rw [F0_eq hG he, mem_insert, mem_insert] at hx'
  rcases hx' with rfl | rfl | hxI
  · -- `x = a`: its two neighbours in `A` are `b` and `s`
    have hsub : ({b, s} : Finset V) ⊆ A.filter (G.Adj x) := by
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact mem_filter.2 ⟨hbA, he.adj⟩
      · exact mem_filter.2 ⟨hIA hsI, has⟩
    have hcard : ({b, s} : Finset V).card = 2 := by
      rw [card_insert_of_notMem (by simp; rintro rfl; exact b_notMem hsI), card_singleton]
    have heq := eq_of_subset_of_card_le hsub (by rw [hcard, hA2 x haA])
    have : y ∈ ({b, s} : Finset V) := by rw [heq]; exact mem_filter.2 ⟨hyA, hxy⟩
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl
    · exact mem_F0.2 ⟨he.lt.le, le_rfl⟩
    · rw [F0_eq hG he]; simp [hsI]
  · have hsub : ({a, q} : Finset V) ⊆ A.filter (G.Adj x) := by
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact mem_filter.2 ⟨haA, he.adj.symm⟩
      · exact mem_filter.2 ⟨hIA hqI, hqb.symm⟩
    have hcard : ({a, q} : Finset V).card = 2 := by
      rw [card_insert_of_notMem (by simp; rintro rfl; exact a_notMem hqI), card_singleton]
    have heq := eq_of_subset_of_card_le hsub (by rw [hcard, hA2 x hbA])
    have : y ∈ ({a, q} : Finset V) := by rw [heq]; exact mem_filter.2 ⟨hyA, hxy⟩
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl
    · exact mem_F0.2 ⟨le_rfl, he.lt.le⟩
    · rw [F0_eq hG he]; simp [hqI]
  · obtain ⟨-, -, -, -, hall⟩ := inner_nbrs hG he hxI
    obtain ⟨q', s', -, -, hq'F, hs'F, hall'⟩ := inner_nbrs hG he hxI
    rcases (hall' y).1 hxy with rfl | rfl
    · exact hq'F
    · exact hs'F

end

/-! ## Transport of faces along `V' ⊆ V` -/

/-- The inclusion of `V' = {x // x ∉ I}` into `V`. -/
def incl (I : Finset V) : {x // x ∉ I} ↪ V := Function.Embedding.subtype _

lemma isFace_map_iff {I : Finset V} (A' : Finset {x // x ∉ I}) :
    IsFace (subG G I) A' ↔ IsFace G (A'.map (incl I)) := by
  have hfil : ∀ x' : {x // x ∉ I}, (A'.map (incl I)).filter (G.Adj (incl I x')) =
      (A'.filter ((subG G I).Adj x')).map (incl I) := by
    intro x'
    rw [filter_map]
    rfl
  unfold IsFace
  rw [card_map]
  apply and_congr Iff.rfl
  apply and_congr
  · constructor
    · intro h x hx
      obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
      rw [hfil, card_map]; exact h x' hx'
    · intro h x' hx'
      have := h _ (mem_map_of_mem (incl I) hx')
      rwa [hfil, card_map] at this
  · constructor
    · intro h B hB hBne hcl
      rw [mem_powerset] at hB
      set B' := A'.filter (fun x' => x'.1 ∈ B)
      have hBB : B'.map (incl I) = B := by
        ext x
        simp only [mem_map, B', mem_filter, incl, Function.Embedding.coe_subtype]
        constructor
        · rintro ⟨x', ⟨-, h⟩, rfl⟩; exact h
        · intro hx
          obtain ⟨x', hx', rfl⟩ := mem_map.1 (hB hx)
          exact ⟨x', ⟨hx', hx⟩, rfl⟩
      have := h B' (mem_powerset.2 (filter_subset _ _)) (by
        obtain ⟨x, hx⟩ := hBne
        rw [← hBB] at hx
        obtain ⟨x', hx', -⟩ := mem_map.1 hx
        exact ⟨x', hx'⟩) (by
        intro x' hx' y' hy' hxy
        simp only [B', mem_filter] at hx' ⊢
        exact ⟨hy', hcl x'.1 hx'.2 y'.1 (mem_map_of_mem _ hy') hxy⟩)
      rw [← hBB, this]
    · intro h B' hB' hBne hcl
      rw [mem_powerset] at hB'
      have := h (B'.map (incl I)) (mem_powerset.2 (map_subset_map.2 hB'))
        (hBne.map) (by
          intro x hx y hy hxy
          obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
          obtain ⟨y', hy', rfl⟩ := mem_map.1 hy
          exact mem_map_of_mem _ (hcl x' hx' y' hy' hxy))
      exact map_injective (incl I) this

/-- The embedding of face sets. -/
def faceEmb (I : Finset V) : Finset {x // x ∉ I} ↪ Finset V :=
  ⟨fun A' => A'.map (incl I), map_injective (incl I)⟩

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

theorem faces_decomp :
    faces G = insert (F0 pos a b) ((faces (subG G (btw pos a b))).map (faceEmb (btw pos a b))) := by
  ext A
  simp only [faces, mem_insert, mem_filter, mem_univ, true_and, mem_map, faceEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hA
    by_cases hmeet : (A ∩ btw pos a b).Nonempty
    · exact Or.inl (face_eq_F0 hG he hA hmeet)
    · right
      have hdis : ∀ x ∈ A, x ∉ btw pos a b := fun x hx hxI => hmeet ⟨x, mem_inter.2 ⟨hx, hxI⟩⟩
      refine ⟨univ.filter (fun x' => x'.1 ∈ A), ?_, ?_⟩
      · have hmap : (univ.filter (fun x' : {x // x ∉ btw pos a b} => x'.1 ∈ A)).map
            (incl (btw pos a b)) = A := by
          ext x
          simp only [mem_map, mem_filter, mem_univ, true_and, incl, Function.Embedding.coe_subtype]
          constructor
          · rintro ⟨x', hx', rfl⟩; exact hx'
          · intro hx; exact ⟨⟨x, hdis x hx⟩, hx, rfl⟩
        rw [isFace_map_iff, hmap]; exact hA
      · ext x
        simp only [mem_map, mem_filter, mem_univ, true_and, incl, Function.Embedding.coe_subtype]
        constructor
        · rintro ⟨x', hx', rfl⟩; exact hx'
        · intro hx; exact ⟨⟨x, hdis x hx⟩, hx, rfl⟩
  · rintro (rfl | ⟨A', hA', rfl⟩)
    · exact isFace_F0 hG he
    · exact (isFace_map_iff A').1 hA'

lemma F0_notMem_image :
    F0 pos a b ∉ (faces (subG G (btw pos a b))).map (faceEmb (btw pos a b)) := by
  intro h
  obtain ⟨A', -, hA'⟩ := mem_map.1 h
  obtain ⟨c, hc⟩ := he.ne
  have hcF : c ∈ F0 pos a b := by rw [F0_eq hG he]; simp [hc]
  rw [← hA'] at hcF
  obtain ⟨c', -, hc'⟩ := mem_map.1 hcF
  have h1 : c'.1 = c := hc'
  exact c'.2 (h1 ▸ hc)

end

end Drac
```

### `DissE.lean`

```lean
import DissD

/-!
# The count for position dissections

`|D(G)| = 2^{1 + ∑_F (|F| - 3)} ∏_F |F|` over the faces (induced cycles) of `G`.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

/-- The decidability instance does not matter. -/
lemma draconian_inst {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (i₁ i₂ : DecidableRel G.Adj) : @draconian V _ _ G i₁ = @draconian V _ _ G i₂ := by
  congr

lemma faces_inst {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (i₁ i₂ : DecidableRel G.Adj) : @faces V _ _ G i₁ = @faces V _ _ G i₂ := by
  congr

lemma card_draconian_top2 : (draconian (⊤ : SimpleGraph (Fin 2))).card = 2 := by decide

open scoped Classical

universe u

theorem count_PD (n : ℕ) : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (pos : V → ℕ), Fintype.card V = n → 2 ≤ n → PD G pos →
    (draconian G).card = 2 ^ (1 + ∑ F ∈ faces G, (F.card - 3)) * ∏ F ∈ faces G, F.card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G pos hn h2 hG
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · -- two vertices: a single edge, no faces
    have hfaces : faces G = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro A hA
      simp only [faces, mem_filter, mem_univ, true_and] at hA
      have := card_le_univ A
      have := hA.1
      omega
    rw [hfaces, sum_empty, prod_empty]
    norm_num
    have e := Fintype.equivFinOfCardEq hn
    rw [card_draconian_congr (⊤ : SimpleGraph (Fin 2)) e (fun x y => ?_)]
    · rw [draconian_inst (⊤ : SimpleGraph (Fin 2)) _ (fun a b => SimpleGraph.Top.adjDecidable _ a b)]
      exact card_draconian_top2
    · rw [SimpleGraph.top_adj, ne_eq, e.injective.eq_iff]
      constructor
      · intro hxy
        rcases lt_or_gt_of_ne (fun h => hxy (hG.inj h)) with hl | hl
        · refine hG.ends x y hxy (fun z => ?_)
          have : z = x ∨ z = y := by
            by_contra hc; push Not at hc
            have hsub : ({x, y, z} : Finset V) ⊆ univ := subset_univ _
            have := card_le_card hsub
            rw [card_univ, hn, card_insert_of_notMem (by simp [hxy, hc.1.symm]),
              card_insert_of_notMem (by simp [hc.2.symm]), card_singleton] at this
            omega
          rcases this with rfl | rfl <;> omega
        · refine (hG.ends y x (Ne.symm hxy) (fun z => ?_)).symm
          have : z = x ∨ z = y := by
            by_contra hc; push Not at hc
            have hsub : ({x, y, z} : Finset V) ⊆ univ := subset_univ _
            have := card_le_card hsub
            rw [card_univ, hn, card_insert_of_notMem (by simp [hxy, hc.1.symm]),
              card_insert_of_notMem (by simp [hc.2.symm]), card_singleton] at this
            omega
          rcases this with rfl | rfl <;> omega
      · intro h hxy; subst hxy; exact G.irrefl h
  · obtain ⟨a, b, he⟩ := exists_minEar hG (hn ▸ h3)
    have hstep := ear_step hG he
    have hlt := card_sub_lt hG he
    have h2' := two_le_card_sub hG he
    have IH := ih _ (hn ▸ hlt) (subG G (btw pos a b)) (fun x => pos x.1) rfl h2' (PD_sub hG he)
    rw [faces_decomp hG he, sum_insert (F0_notMem_image hG he), prod_insert (F0_notMem_image hG he),
      sum_map, prod_map, card_F0 hG he]
    simp only [faceEmb, Function.Embedding.coeFn_mk, card_map]
    rw [IH] at hstep
    set p := (btw pos a b).card
    have hp : 1 ≤ p := card_pos.2 he.ne
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hq] at hstep ⊢
    rw [show q + 1 + 2 - 3 = q by omega]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [hstep]
    rw [pow_add, pow_add, pow_add, pow_succ]
    ring

end Drac
```

### `DissF.lean`

```lean
import DissE

/-!
# The extended-weak-dual degree of a face equals its length

For a position dissection, an *outer pair* is a pair `(x, y)` with `pos x < pos y` that is
positionally consecutive or is (first, last).  The degree of `v_F` in the extended weak dual
is the number of other faces sharing an edge with `F` plus the number of outer pairs inside
`F`.  We prove it equals `|F|`, together with: every outer pair lies in exactly one face.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {pos : V → ℕ}

/-- Outer pairs: edges of the outer cycle. -/
def OP (pos : V → ℕ) (x y : V) : Prop :=
  pos x < pos y ∧ (btw pos x y = ∅ ∨ ∀ z, pos x ≤ pos z ∧ pos z ≤ pos y)

noncomputable def outerP (pos : V → ℕ) : Finset (V × V) := univ.filter (fun e => OP pos e.1 e.2)

/-- Two vertex sets share an edge of `G`. -/
def share (G : SimpleGraph V) (F F' : Finset V) : Prop :=
  ∃ x ∈ F, ∃ y ∈ F, G.Adj x y ∧ x ∈ F' ∧ y ∈ F'

/-- Extended-weak-dual degree (abstract positions). -/
noncomputable def ewdA (G : SimpleGraph V) (pos : V → ℕ) (F : Finset V) : ℕ :=
  ((faces G).filter (fun F' => F' ≠ F ∧ share G F F')).card +
    ((outerP pos).filter (fun e => e.1 ∈ F ∧ e.2 ∈ F)).card

/-- The invariant. -/
def Inv (G : SimpleGraph V) (pos : V → ℕ) : Prop :=
  (∀ F ∈ faces G, ewdA G pos F = F.card) ∧
    (3 ≤ Fintype.card V → ∀ x y, OP pos x y → ((faces G).filter (fun F => x ∈ F ∧ y ∈ F)).card = 1)

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

/-- Counting faces of `G` with a property. -/
lemma card_faces_filter (Q : Finset V → Prop) [DecidablePred Q] :
    ((faces G).filter Q).card = (if Q (F0 pos a b) then 1 else 0) +
      ((faces (subG G (btw pos a b))).filter (fun A' => Q (A'.map (incl (btw pos a b))))).card := by
  rw [faces_decomp hG he, filter_insert, filter_map]
  have hnot := F0_notMem_image hG he
  split_ifs with hQ
  · rw [card_insert_of_notMem (fun h => hnot (mem_of_subset (map_subset_map.2 (filter_subset _ _))
      h)), card_map]
    simp only [faceEmb, Function.Embedding.coeFn_mk]
    ring_nf; rfl
  · rw [card_map, zero_add]; rfl

lemma mem_map_incl {A' : Finset {x // x ∉ btw pos a b}} {x : V} :
    x ∈ A'.map (incl (btw pos a b)) ↔ ∃ h : x ∉ btw pos a b, (⟨x, h⟩ : {x // x ∉ btw pos a b}) ∈ A' := by
  simp only [mem_map, incl, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨x', hx', rfl⟩; exact ⟨x'.2, hx'⟩
  · rintro ⟨h, hx⟩; exact ⟨_, hx, rfl⟩

lemma F0_inter_V' {x : V} (hx : x ∈ F0 pos a b) (hxI : x ∉ btw pos a b) : x = a ∨ x = b := by
  rw [F0_eq hG he, mem_insert, mem_insert] at hx
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hxI

/-- Outer pairs touching an inner vertex are consecutive pairs inside `F₀`. -/
lemma OP_inner {x y : V} (hI : x ∈ btw pos a b ∨ y ∈ btw pos a b) (h : OP pos x y) :
    x ∈ F0 pos a b ∧ y ∈ F0 pos a b ∧ btw pos x y = ∅ := by
  obtain ⟨hlt, h⟩ := h
  have hlt' := he.lt
  have hemp : btw pos x y = ∅ := by
    rcases h with h | h
    · exact h
    · exfalso
      rcases hI with hx | hy
      · have := (h a).1; have := mem_btw.1 hx; omega
      · have := (h b).2; have := mem_btw.1 hy; omega
  refine ⟨?_, ?_, hemp⟩
  · rcases hI with hx | hy
    · have := mem_btw.1 hx; rw [mem_F0]; omega
    · have hy' := mem_btw.1 hy
      have := pred_ge_of hG.inj hlt hemp hy'.1
      rw [mem_F0]; omega
  · rcases hI with hx | hy
    · have hx' := mem_btw.1 hx
      have := succ_le_of hG he hlt hemp hx'.2
      rw [mem_F0]; omega
    · have := mem_btw.1 hy; rw [mem_F0]; omega

/-- Outer pairs of `G'` versus outer pairs of `G`. -/
lemma OP_sub_iff (x y : {x // x ∉ btw pos a b}) :
    OP (fun x => pos x.1) x y ↔ OP pos x.1 y.1 ∨ (x.1 = a ∧ y.1 = b) := by
  have hlt := he.lt
  constructor
  · rintro ⟨hxy, h | h⟩
    · by_cases hb : btw pos x.1 y.1 = ∅
      · exact Or.inl ⟨hxy, Or.inl hb⟩
      · right
        obtain ⟨w, hw⟩ := nonempty_iff_ne_empty.2 hb
        have hw' := mem_btw.1 hw
        have hwI : w ∈ btw pos a b := by
          by_contra hwI
          have : (⟨w, hwI⟩ : {x // x ∉ btw pos a b}) ∈ btw (fun x => pos x.1) x y := mem_btw.2 hw'
          rw [h] at this; simp at this
        have hwI' := mem_btw.1 hwI
        have ha : ¬(pos x.1 < pos a ∧ pos a < pos y.1) := fun hh => by
          have : (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ btw (fun x => pos x.1) x y := mem_btw.2 hh
          rw [h] at this; simp at this
        have hb' : ¬(pos x.1 < pos b ∧ pos b < pos y.1) := fun hh => by
          have : (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ btw (fun x => pos x.1) x y := mem_btw.2 hh
          rw [h] at this; simp at this
        have hx := x.2; have hy := y.2
        rw [mem_btw] at hx hy
        exact ⟨hG.inj (by omega), hG.inj (by omega)⟩
    · left
      refine ⟨hxy, Or.inr (fun z => ?_)⟩
      by_cases hz : z ∈ btw pos a b
      · have := mem_btw.1 hz
        have := h ⟨a, a_notMem⟩; have := h ⟨b, b_notMem⟩
        simp only at *; constructor <;> omega
      · exact h ⟨z, hz⟩
  · rintro (⟨hxy, h | h⟩ | ⟨hx, hy⟩)
    · refine ⟨hxy, Or.inl ?_⟩
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      have hw' : pos x.1 < pos w.1 ∧ pos w.1 < pos y.1 :=
        (mem_btw (pos := fun x : {x // x ∉ btw pos a b} => pos x.1)).1 hw
      have : w.1 ∈ btw pos x.1 y.1 := mem_btw.2 hw'
      rw [h] at this; simp at this
    · exact ⟨hxy, Or.inr (fun z => h z.1)⟩
    · refine ⟨by show pos x.1 < pos y.1; rw [hx, hy]; exact hlt, Or.inl ?_⟩
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      have hw' : pos x.1 < pos w.1 ∧ pos w.1 < pos y.1 :=
        (mem_btw (pos := fun x : {x // x ∉ btw pos a b} => pos x.1)).1 hw
      rw [hx, hy] at hw'
      exact w.2 (mem_btw.2 hw')

lemma OP_ab_iff : OP pos a b ↔ ∀ z, pos a ≤ pos z ∧ pos z ≤ pos b := by
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h (nonempty_iff_ne_empty.1 he.ne)
    · exact h
  · intro h; exact ⟨he.lt, Or.inr h⟩

lemma not_OP_ab (h3 : 3 ≤ Fintype.card {x // x ∉ btw pos a b}) : ¬ OP pos a b := by
  rw [OP_ab_iff hG he]
  intro hall
  -- every vertex of `V'` is `a` or `b`
  have hsub : (univ : Finset {x // x ∉ btw pos a b}) ⊆ {⟨a, a_notMem⟩, ⟨b, b_notMem⟩} := by
    intro x _
    have := F0_inter_V' hG he (x := x.1) (mem_F0.2 (hall x.1)) x.2
    rcases this with h | h
    · simp [Subtype.ext_iff, h]
    · simp [Subtype.ext_iff, h]
  have := card_le_card hsub
  rw [card_univ] at this
  have := card_le_two (a := (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b})) (b := ⟨b, b_notMem⟩)
  omega

/-- Consecutive pairs inside `F₀`: there are `|F₀| - 1` of them. -/
lemma card_consec_F0 :
    ((univ : Finset (V × V)).filter (fun e => e.1 ∈ F0 pos a b ∧ e.2 ∈ F0 pos a b ∧
      pos e.1 < pos e.2 ∧ btw pos e.1 e.2 = ∅)).card + 1 = (F0 pos a b).card := by
  have hb : b ∈ F0 pos a b := mem_F0.2 ⟨he.lt.le, le_rfl⟩
  rw [← card_erase_add_one hb]
  congr 1
  apply card_bij (fun e _ => e.1)
  · intro e he'
    simp only [mem_filter, mem_univ, true_and] at he'
    obtain ⟨h1, h2, h3, -⟩ := he'
    rw [mem_erase]
    refine ⟨fun h => ?_, h1⟩
    rw [mem_F0] at h2; rw [h] at h3; omega
  · intro e₁ h₁ e₂ h₂ h
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    have h' : e₁.1 = e₂.1 := h
    have := consec_unique_up hG he h₁.2.2.1 h₁.2.2.2 (h' ▸ h₂.2.2.1) (h' ▸ h₂.2.2.2)
    exact Prod.ext h' this
  · intro x hx
    rw [mem_erase] at hx
    have hx' := mem_F0.1 hx.2
    have hxb : pos x < pos b := lt_of_le_of_ne hx'.2 (fun h => hx.1 (hG.inj h))
    obtain ⟨s, hs1, hs2⟩ := exists_succ hG he x ⟨b, hxb⟩
    have := succ_le_of hG he hs1 hs2 hxb
    exact ⟨(x, s), by simp only [mem_filter, mem_univ, true_and]; exact ⟨hx.2, mem_F0.2 ⟨by omega,
      this⟩, hs1, hs2⟩, rfl⟩

end

end Drac
```

### `DissG.lean`

```lean
import DissF

/-!
# The invariant: `deg_{B^(**)}(v_F) = |F|` and outer pairs lie in exactly one face
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {pos : V → ℕ}

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

lemma all_F0_of_two (h2 : Fintype.card {x // x ∉ btw pos a b} = 2) (z : V) : z ∈ F0 pos a b := by
  by_cases hz : z ∈ btw pos a b
  · rw [F0_eq hG he]; simp [hz]
  · have hab : (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ≠ ⟨b, b_notMem⟩ := fun h => by
      have := congrArg Subtype.val h; simp only at this
      have := he.lt; rw [‹a = b›] at this; omega
    have huniv : (univ : Finset {x // x ∉ btw pos a b}) = {⟨a, a_notMem⟩, ⟨b, b_notMem⟩} := by
      symm; apply eq_of_subset_of_card_le (subset_univ _)
      rw [card_univ, h2, card_insert_of_notMem (by simpa using hab), card_singleton]
    have : (⟨z, hz⟩ : {x // x ∉ btw pos a b}) ∈ ({⟨a, a_notMem⟩, ⟨b, b_notMem⟩} :
        Finset {x // x ∉ btw pos a b}) := huniv ▸ mem_univ _
    simp only [mem_insert, mem_singleton, Subtype.mk.injEq] at this
    rcases this with rfl | rfl
    · exact mem_F0.2 ⟨le_rfl, he.lt.le⟩
    · exact mem_F0.2 ⟨he.lt.le, le_rfl⟩

lemma faces_sub_empty (h2 : Fintype.card {x // x ∉ btw pos a b} = 2) :
    faces (subG G (btw pos a b)) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro A hA
  simp only [faces, mem_filter, mem_univ, true_and] at hA
  have := card_le_univ A
  have := hA.1
  omega

lemma three_le_of_face {A' : Finset {x // x ∉ btw pos a b}} (hA : A' ∈ faces (subG G (btw pos a b))) :
    3 ≤ Fintype.card {x // x ∉ btw pos a b} := by
  simp only [faces, mem_filter, mem_univ, true_and] at hA
  exact hA.1.trans (card_le_univ _)

/-- Outer pairs inside `F₀`. -/
lemma card_OP_F0 :
    ((outerP pos).filter (fun e => e.1 ∈ F0 pos a b ∧ e.2 ∈ F0 pos a b)).card + 1 =
      (F0 pos a b).card + (if OP pos a b then 1 else 0) := by
  rw [← card_consec_F0 hG he]
  have heq : (outerP pos).filter (fun e => e.1 ∈ F0 pos a b ∧ e.2 ∈ F0 pos a b) =
      ((univ : Finset (V × V)).filter (fun e => e.1 ∈ F0 pos a b ∧ e.2 ∈ F0 pos a b ∧
        pos e.1 < pos e.2 ∧ btw pos e.1 e.2 = ∅)) ∪ (if OP pos a b then {(a, b)} else ∅) := by
    ext ⟨x, y⟩
    simp only [outerP, mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨⟨hxy, h | h⟩, hx, hy⟩
      · exact Or.inl ⟨hx, hy, hxy, h⟩
      · right
        have hx' := mem_F0.1 hx; have hy' := mem_F0.1 hy
        have h1 := (h a).1; have h2 := (h b).2
        have hxa : x = a := hG.inj (by omega)
        have hyb : y = b := hG.inj (by omega)
        subst hxa hyb
        rw [if_pos ⟨hxy, Or.inr h⟩]; simp
    · rintro (⟨hx, hy, hxy, h⟩ | h)
      · exact ⟨⟨hxy, Or.inl h⟩, hx, hy⟩
      · split_ifs at h with hab
        · simp only [mem_singleton, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hab, mem_F0.2 ⟨le_rfl, he.lt.le⟩, mem_F0.2 ⟨he.lt.le, le_rfl⟩⟩
        · simp at h
  rw [heq, card_union_of_disjoint]
  · split_ifs <;> simp
  · rw [disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1
    split_ifs at h2
    · simp only [mem_singleton, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact absurd h1.2.2.2 (nonempty_iff_ne_empty.1 he.ne)
    · simp at h2

/-- Sharing an edge with `F₀`. -/
lemma share_F0_iff (A' : Finset {x // x ∉ btw pos a b}) :
    share G (F0 pos a b) (A'.map (incl (btw pos a b))) ↔
      (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧ (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hxA, hyA⟩
    obtain ⟨hxI, hx'⟩ := (mem_map_incl hG he).1 hxA
    obtain ⟨hyI, hy'⟩ := (mem_map_incl hG he).1 hyA
    rcases F0_inter_V' hG he hx hxI with rfl | rfl <;>
      rcases F0_inter_V' hG he hy hyI with rfl | rfl
    · exact absurd hxy G.irrefl
    · exact ⟨hx', hy'⟩
    · exact ⟨hy', hx'⟩
    · exact absurd hxy G.irrefl
  · rintro ⟨ha, hb⟩
    exact ⟨a, mem_F0.2 ⟨le_rfl, he.lt.le⟩, b, mem_F0.2 ⟨he.lt.le, le_rfl⟩, he.adj,
      (mem_map_incl hG he).2 ⟨a_notMem, ha⟩, (mem_map_incl hG he).2 ⟨b_notMem, hb⟩⟩

lemma share_F0_iff' (A' : Finset {x // x ∉ btw pos a b}) :
    share G (A'.map (incl (btw pos a b))) (F0 pos a b) ↔
      (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧ (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' := by
  rw [← share_F0_iff hG he]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hx', hy'⟩; exact ⟨x, hx', y, hy', hxy, hx, hy⟩
  · rintro ⟨x, hx, y, hy, hxy, hx', hy'⟩; exact ⟨x, hx', y, hy', hxy, hx, hy⟩

lemma share_map_iff (A' B' : Finset {x // x ∉ btw pos a b}) :
    share G (A'.map (incl (btw pos a b))) (B'.map (incl (btw pos a b))) ↔
      share (subG G (btw pos a b)) A' B' := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hxB, hyB⟩
    obtain ⟨x', hx', rfl⟩ := mem_map.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_map.1 hy
    exact ⟨x', hx', y', hy', hxy, (mem_map' _).1 hxB, (mem_map' _).1 hyB⟩
  · rintro ⟨x, hx, y, hy, hxy, hxB, hyB⟩
    exact ⟨_, mem_map_of_mem _ hx, _, mem_map_of_mem _ hy, hxy, mem_map_of_mem _ hxB,
      mem_map_of_mem _ hyB⟩

end

end Drac
```

### `DissH.lean`

```lean
import DissG

/-!
# The invariant by induction
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Drac

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {pos : V → ℕ}

section
variable {a b : V} (hG : PD G pos) (he : MinEar G pos a b)
include hG he

/-- Outer pairs inside an old face. -/
lemma card_OP_map (h3 : 3 ≤ Fintype.card {x // x ∉ btw pos a b}) (A' : Finset {x // x ∉ btw pos a b}) :
    ((outerP pos).filter (fun e => e.1 ∈ A'.map (incl (btw pos a b)) ∧
        e.2 ∈ A'.map (incl (btw pos a b)))).card +
      (if (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧
          (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' then 1 else 0) =
      ((outerP (fun x : {x // x ∉ btw pos a b} => pos x.1)).filter
        (fun e => e.1 ∈ A' ∧ e.2 ∈ A')).card := by
  have hnab := not_OP_ab hG he h3
  set T := (outerP (fun x : {x // x ∉ btw pos a b} => pos x.1)).filter (fun e => e.1 ∈ A' ∧ e.2 ∈ A')
  have hsplit : T = T.filter (fun e => OP pos e.1.1 e.2.1) ∪
      T.filter (fun e => e.1.1 = a ∧ e.2.1 = b) := by
    ext e
    simp only [mem_union, mem_filter, T, outerP, mem_univ, true_and]
    constructor
    · rintro ⟨hOP, h⟩
      rcases (OP_sub_iff hG he e.1 e.2).1 hOP with h' | h'
      · exact Or.inl ⟨⟨hOP, h⟩, h'⟩
      · exact Or.inr ⟨⟨hOP, h⟩, h'⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  rw [hsplit, card_union_of_disjoint]
  · congr 1
    · symm
      apply card_bij (fun (e : {x // x ∉ btw pos a b} × {x // x ∉ btw pos a b}) _ => ((e.1 : V), (e.2 : V)))
      · intro e he'
        simp only [mem_filter, T, outerP, mem_univ, true_and] at he' ⊢
        exact ⟨he'.2, (mem_map_incl hG he).2 ⟨e.1.2, he'.1.2.1⟩,
          (mem_map_incl hG he).2 ⟨e.2.2, he'.1.2.2⟩⟩
      · intro e₁ _ e₂ _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
      · rintro ⟨x, y⟩ h
        simp only [mem_filter, outerP, mem_univ, true_and] at h
        obtain ⟨hOP, hx, hy⟩ := h
        obtain ⟨hxI, hx'⟩ := (mem_map_incl hG he).1 hx
        obtain ⟨hyI, hy'⟩ := (mem_map_incl hG he).1 hy
        refine ⟨(⟨x, hxI⟩, ⟨y, hyI⟩), ?_, rfl⟩
        simp only [mem_filter, T, outerP, mem_univ, true_and]
        exact ⟨⟨(OP_sub_iff hG he _ _).2 (Or.inl hOP), hx', hy'⟩, hOP⟩
    · symm
      split_ifs with hab
      · rw [card_eq_one]
        refine ⟨(⟨a, a_notMem⟩, ⟨b, b_notMem⟩), ?_⟩
        ext e
        simp only [mem_filter, T, outerP, mem_univ, true_and, mem_singleton]
        constructor
        · rintro ⟨-, h1, h2⟩; exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
        · rintro rfl
          exact ⟨⟨(OP_sub_iff hG he _ _).2 (Or.inr ⟨rfl, rfl⟩), hab⟩, rfl, rfl⟩
      · rw [card_eq_zero, filter_eq_empty_iff]
        rintro e he' ⟨h1, h2⟩
        simp only [mem_filter, T] at he'
        apply hab
        have e1 : e.1 = ⟨a, a_notMem⟩ := Subtype.ext h1
        have e2 : e.2 = ⟨b, b_notMem⟩ := Subtype.ext h2
        exact ⟨e1 ▸ he'.2.1, e2 ▸ he'.2.2⟩
  · rw [disjoint_filter]
    rintro e - h ⟨h1, h2⟩
    rw [h1, h2] at h
    exact hnab h

/-- The invariant passes from `G'` to `G`. -/
theorem inv_step (IH : Inv (subG G (btw pos a b)) (fun x => pos x.1)) : Inv G pos := by
  have hnot := F0_notMem_image hG he
  refine ⟨fun F hF => ?_, fun h3V x y hxy => ?_⟩
  · rw [faces_decomp hG he, mem_insert] at hF
    rcases hF with rfl | hF
    · -- the new face
      unfold ewdA
      rw [card_faces_filter hG he, if_neg (by simp)]
      have hfil : (faces (subG G (btw pos a b))).filter (fun A' => A'.map (incl (btw pos a b)) ≠ F0 pos a b ∧
          share G (F0 pos a b) (A'.map (incl (btw pos a b)))) =
          (faces (subG G (btw pos a b))).filter (fun A' => (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧ (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A') := by
        apply filter_congr
        intro A' hA'
        rw [share_F0_iff hG he]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨fun h' => hnot (mem_map.2 ⟨A', hA', ?_⟩), h⟩
          simpa [faceEmb] using h'
      rw [hfil]
      have hOP := card_OP_F0 hG he
      by_cases h3' : 3 ≤ Fintype.card {x // x ∉ btw pos a b}
      · rw [if_neg (not_OP_ab hG he h3')] at hOP
        have := IH.2 h3' ⟨a, a_notMem⟩ ⟨b, b_notMem⟩ ((OP_sub_iff hG he _ _).2 (Or.inr ⟨rfl, rfl⟩))
        omega
      · have h2 : Fintype.card {x // x ∉ btw pos a b} = 2 := by have := two_le_card_sub hG he; omega
        rw [if_pos ((OP_ab_iff hG he).2 (fun z => mem_F0.1 (all_F0_of_two hG he h2 z)))] at hOP
        have hE : faces (subG G (btw pos a b)) = ∅ := faces_sub_empty hG he h2
        rw [hE, filter_empty, card_empty]
        omega
    · obtain ⟨A', hA', rfl⟩ := mem_map.1 hF
      simp only [faceEmb, Function.Embedding.coeFn_mk]
      have h3' := three_le_of_face hG he hA'
      unfold ewdA
      rw [card_faces_filter hG he]
      have hQF0 : (F0 pos a b ≠ A'.map (incl (btw pos a b)) ∧ share G (A'.map (incl (btw pos a b))) (F0 pos a b)) ↔
          ((⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧ (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A') := by
        rw [share_F0_iff' hG he]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨fun h' => hnot (mem_map.2 ⟨A', hA', ?_⟩), h⟩
          simpa [faceEmb] using h'.symm
      have hfil : (faces (subG G (btw pos a b))).filter (fun B' => B'.map (incl (btw pos a b)) ≠ A'.map (incl (btw pos a b)) ∧
          share G (A'.map (incl (btw pos a b))) (B'.map (incl (btw pos a b)))) =
          (faces (subG G (btw pos a b))).filter (fun B' => B' ≠ A' ∧ share (subG G (btw pos a b)) A' B') := by
        apply filter_congr
        intro B' _
        rw [share_map_iff hG he, (map_injective (incl (btw pos a b))).ne_iff]
      rw [hfil]
      have hIH := IH.1 A' hA'
      unfold ewdA at hIH
      have hmap := card_OP_map hG he h3' A'
      rw [card_map]
      by_cases hab : (⟨a, a_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧ (⟨b, b_notMem⟩ : {x // x ∉ btw pos a b}) ∈ A'
      · rw [if_pos (hQF0.2 hab)]
        rw [if_pos hab] at hmap
        omega
      · rw [if_neg (fun h => hab (hQF0.1 h))]
        rw [if_neg hab] at hmap
        omega
  · -- outer pairs lie in exactly one face
    rw [card_faces_filter hG he]
    by_cases hI : x ∈ btw pos a b ∨ y ∈ btw pos a b
    · obtain ⟨hx, hy, -⟩ := OP_inner hG he hI hxy
      rw [if_pos ⟨hx, hy⟩]
      have : (faces (subG G (btw pos a b))).filter (fun A' => x ∈ A'.map (incl (btw pos a b)) ∧ y ∈ A'.map (incl (btw pos a b))) = ∅ := by
        rw [filter_eq_empty_iff]
        rintro A' - ⟨h1, h2⟩
        rcases hI with h | h
        · obtain ⟨hxI, -⟩ := (mem_map_incl hG he).1 h1; exact hxI h
        · obtain ⟨hyI, -⟩ := (mem_map_incl hG he).1 h2; exact hyI h
      rw [this, card_empty]
    · push Not at hI
      by_cases h3' : 3 ≤ Fintype.card {x // x ∉ btw pos a b}
      · have hOP' := (OP_sub_iff hG he ⟨x, hI.1⟩ ⟨y, hI.2⟩).2 (Or.inl hxy)
        have := IH.2 h3' _ _ hOP'
        have hF0 : ¬(x ∈ F0 pos a b ∧ y ∈ F0 pos a b) := by
          rintro ⟨hx, hy⟩
          have hxy' := hxy.1
          rcases F0_inter_V' hG he hx hI.1 with rfl | rfl <;>
            rcases F0_inter_V' hG he hy hI.2 with rfl | rfl
          · omega
          · exact not_OP_ab hG he h3' hxy
          · have := he.lt; omega
          · omega
        rw [if_neg hF0]
        have hfil : (faces (subG G (btw pos a b))).filter (fun A' => x ∈ A'.map (incl (btw pos a b)) ∧ y ∈ A'.map (incl (btw pos a b))) =
            (faces (subG G (btw pos a b))).filter (fun A' => (⟨x, hI.1⟩ : {x // x ∉ btw pos a b}) ∈ A' ∧ (⟨y, hI.2⟩ : {x // x ∉ btw pos a b}) ∈ A') := by
          apply filter_congr
          intro A' _
          rw [mem_map_incl hG he, mem_map_incl hG he]
          try simp only [exists_prop]
          constructor
          · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨hI.1, h1⟩, ⟨hI.2, h2⟩⟩
        rw [hfil]
        omega
      · have h2 : Fintype.card {x // x ∉ btw pos a b} = 2 := by have := two_le_card_sub hG he; omega
        rw [if_pos ⟨all_F0_of_two hG he h2 x, all_F0_of_two hG he h2 y⟩, faces_sub_empty hG he h2,
          filter_empty, card_empty]

end

universe u

theorem inv_PD (n : ℕ) : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (pos : V → ℕ), Fintype.card V = n → 2 ≤ n → PD G pos → Inv G pos := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G pos hn h2 hG
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · refine ⟨fun F hF => ?_, fun h => by omega⟩
    simp only [faces, mem_filter, mem_univ, true_and] at hF
    have := card_le_univ F
    have := hF.1
    omega
  · obtain ⟨a, b, he⟩ := exists_minEar hG (hn ▸ h3)
    exact inv_step hG he (ih _ (hn ▸ card_sub_lt hG he) (subG G (btw pos a b)) (fun x => pos x.1)
      rfl (two_le_card_sub hG he) (PD_sub hG he))

end Drac
```

### `Endpoint.lean`

```lean
import DissH

/-!
# The endpoint: Davis–Chen Conjecture 36 (block form)
-/

set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Finset

namespace Dissection

variable {n : ℕ}

lemma adj_lt_cases (D : Dissection n) {i j : Fin n} (h : D.graph.Adj i j) (hij : i.val < j.val) :
    j.val = i.val + 1 ∨ (i.val = 0 ∧ j.val = n - 1) ∨ (i, j) ∈ D.chords := by
  obtain ⟨-, h⟩ := h
  rcases h with h | h | h
  · unfold outerAdj at h; omega
  · exact Or.inr (Or.inr h)
  · have := (D.isChord _ h).1; simp only at this; omega

/-- A dissection is a position dissection for the positions `0, …, n-1`. -/
theorem pd (D : Dissection n) (hn : 2 ≤ n) : Drac.PD D.graph (fun i => i.val) := by
  refine ⟨Fin.val_injective, ?_, ?_, ?_⟩
  · intro a b c d hab hcd h
    obtain ⟨h1, h2, h3⟩ := h
    dsimp only at h1 h2 h3
    have hb := b.isLt; have hd := d.isLt
    rcases adj_lt_cases D hab (by omega) with h | h | hab'
    · omega
    · omega
    rcases adj_lt_cases D hcd (by omega) with h | h | hcd'
    · omega
    · omega
    exact D.noncross _ hab' _ hcd' ⟨h1, h2, h3⟩
  · intro i j hij hnone
    try dsimp only at hij hnone
    refine ⟨fun h => by rw [h] at hij; omega, Or.inl ?_⟩
    unfold outerAdj
    left
    by_contra hc
    exact hnone ⟨i.val + 1, by omega⟩ ⟨by simp, by simp; omega⟩
  · intro i j hij hall
    try dsimp only at hall
    refine ⟨hij, Or.inl ?_⟩
    unfold outerAdj
    have h0 := (hall ⟨0, by omega⟩).1
    have h1 := (hall ⟨n - 1, by omega⟩).2
    have := j.isLt
    simp only at h0 h1
    right; right; left
    exact ⟨by omega, by omega⟩

lemma outerEdges_eq : outerEdges n = Drac.outerP (fun i : Fin n => i.val) := by
  classical
  ext ⟨i, j⟩
  unfold outerEdges Drac.outerP
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and, Drac.OP]
  have hi := i.isLt; have hj := j.isLt
  constructor
  · rintro ⟨hij, h | h⟩
    · refine ⟨hij, Or.inl ?_⟩
      rw [eq_empty_iff_forall_notMem]
      intro z hz
      rw [Drac.mem_btw] at hz
      omega
    · exact ⟨hij, Or.inr (fun z => ⟨by omega, by have := z.isLt; omega⟩)⟩
  · rintro ⟨hij, h | h⟩
    · refine ⟨hij, Or.inl ?_⟩
      by_contra hc
      have : (⟨i.val + 1, by omega⟩ : Fin n) ∈ Drac.btw (fun i : Fin n => i.val) i j :=
        Drac.mem_btw.2 ⟨by simp, by simp; omega⟩
      rw [h] at this; simp at this
    · have h0 := (h ⟨0, by omega⟩).1
      have h1 := (h ⟨n - 1, by omega⟩).2
      simp only at h0 h1
      exact ⟨hij, Or.inr ⟨by omega, by omega⟩⟩

/-- The literal degree equals the abstract one. -/
lemma ewdDeg_eq (D : Dissection n) (F : Finset (Fin n)) :
    D.ewdDeg F = Drac.ewdA D.graph (fun i => i.val) F := by
  unfold ewdDeg Drac.ewdA
  rw [outerEdges_eq]
  congr 1
  convert rfl
  all_goals exact Iff.rfl

lemma mem_faces_iff (D : Dissection n) (F : Finset (Fin n)) :
    F ∈ @Drac.faces (Fin n) _ _ D.graph (fun a b => Classical.propDecidable _) ↔ F ∈ Drac.faces D.graph := by
  rw [Drac.faces_inst D.graph (fun a b => Classical.propDecidable _) inferInstance]

theorem main (D : Dissection n) (hn : 3 ≤ n) :
    (Drac.draconian D.graph).card = 2 ^ (1 + D.S).toNat * ∏ F ∈ Drac.faces D.graph, D.ewdDeg F := by
  have hPD := pd D (by omega)
  have hc := Drac.count_PD n D.graph (fun i : Fin n => i.val) (Fintype.card_fin n) (by omega) hPD
  have hinv := (Drac.inv_PD n D.graph (fun i : Fin n => i.val) (Fintype.card_fin n) (by omega) hPD).1
  have hc' : (Drac.draconian D.graph).card =
      2 ^ (1 + ∑ F ∈ Drac.faces D.graph, (F.card - 3)) * ∏ F ∈ Drac.faces D.graph, F.card := by
    convert hc
  have hdeg : ∀ F ∈ Drac.faces D.graph, D.ewdDeg F = F.card := by
    intro F hF
    rw [ewdDeg_eq]
    apply hinv
    convert hF
  have h3 : ∀ F ∈ Drac.faces D.graph, 3 ≤ F.card := by
    intro F hF
    simp only [Drac.faces, mem_filter, mem_univ, true_and] at hF
    exact hF.1
  have hS : (1 + D.S).toNat = 1 + ∑ F ∈ Drac.faces D.graph, (F.card - 3) := by
    unfold S
    have : ∑ F ∈ Drac.faces D.graph, ((D.ewdDeg F : ℤ) - 3) =
        ((∑ F ∈ Drac.faces D.graph, (F.card - 3) : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
      exact sum_congr rfl (fun F hF => by rw [hdeg F hF]; have := h3 F hF; omega)
    rw [this]
    omega
  rw [hc', prod_congr rfl hdeg, hS]

/-- `S(B) ≥ 0`, so the `toNat` in the statement is harmless. -/
theorem S_nonneg (D : Dissection n) (hn : 3 ≤ n) : 0 ≤ D.S := by
  have hPD := pd D (by omega)
  have hinv := (Drac.inv_PD n D.graph (fun i : Fin n => i.val) (Fintype.card_fin n) (by omega) hPD).1
  unfold S
  apply sum_nonneg
  intro F hF
  rw [ewdDeg_eq, hinv F (by convert hF)]
  simp only [Drac.faces, mem_filter, mem_univ, true_and] at hF
  have := hF.1
  omega

end Dissection

/-- **MathDB 347302** (Davis–Chen Conjecture 36, block form). -/
theorem mathdb347302 : Conj36Block := fun n hn D => Dissection.main D hn
```

### `Checks.lean`

```lean
import Endpoint

/-!
# Non-vacuity and kernel checks

Small dissections where both sides of the endpoint are evaluated by `decide` (kernel
reduction only), independently of the proof; and instances of the theorem.
-/

open Dissection

namespace Checks

/-- The triangle. -/
def tri : Dissection 3 := ⟨∅, by simp, by simp⟩
/-- The square with the chord `02`. -/
def sq : Dissection 4 := ⟨{(0, 2)}, by decide, by decide⟩
/-- The pentagon with the chord `02`. -/
def pent1 : Dissection 5 := ⟨{(0, 2)}, by decide, by decide⟩
/-- The pentagon with the chords `02`, `03` (a triangulation). -/
def pent2 : Dissection 5 := ⟨{(0, 2), (0, 3)}, by decide, by decide⟩
/-- The hexagon with the chords `02`, `24`, `04` (inner triangle; not reachable by the source's
recurrences). -/
def hex : Dissection 6 := ⟨{(0, 2), (2, 4), (0, 4)}, by decide, by decide⟩

-- exact counts of draconian sequences, by kernel computation
theorem tri_count : (Drac.draconian tri.graph).card = 6 := by decide
theorem sq_count : (Drac.draconian sq.graph).card = 18 := by decide
set_option maxRecDepth 100000 in
theorem pent1_count : (Drac.draconian pent1.graph).card = 48 := by decide
set_option maxRecDepth 100000 in
theorem pent2_count : (Drac.draconian pent2.graph).card = 54 := by decide

-- the right-hand side of Eq. (9), by kernel computation
theorem tri_rhs : 2 ^ (1 + tri.S).toNat * ∏ F ∈ Drac.faces tri.graph, tri.ewdDeg F = 6 := by decide
theorem sq_rhs : 2 ^ (1 + sq.S).toNat * ∏ F ∈ Drac.faces sq.graph, sq.ewdDeg F = 18 := by decide
theorem pent1_rhs :
    2 ^ (1 + pent1.S).toNat * ∏ F ∈ Drac.faces pent1.graph, pent1.ewdDeg F = 48 := by decide
theorem pent2_rhs :
    2 ^ (1 + pent2.S).toNat * ∏ F ∈ Drac.faces pent2.graph, pent2.ewdDeg F = 54 := by decide
theorem hex_rhs : 2 ^ (1 + hex.S).toNat * ∏ F ∈ Drac.faces hex.graph, hex.ewdDeg F = 162 := by
  decide

-- the faces are what they should be
theorem sq_faces : Drac.faces sq.graph = {{0, 1, 2}, {0, 2, 3}} := by decide
theorem hex_faces_card : (Drac.faces hex.graph).card = 4 := by decide

/-- A consequence of the theorem not reachable by the source's Corollary 35. -/
theorem hex_count : (Drac.draconian hex.graph).card = 162 := by
  rw [mathdb347302 6 (by norm_num) hex, hex_rhs]

/-- The hypotheses are satisfiable for every `n ≥ 3` (the `n`-gon). -/
def polygon (n : ℕ) : Dissection n := ⟨∅, by simp, by simp⟩

theorem polygon_count (n : ℕ) (hn : 3 ≤ n) :
    (Drac.draconian (polygon n).graph).card =
      2 ^ (1 + (polygon n).S).toNat * ∏ F ∈ Drac.faces (polygon n).graph, (polygon n).ewdDeg F :=
  mathdb347302 n hn (polygon n)

end Checks
```

### `Axioms.lean`

```lean
import Checks

/-! Endpoint statements and axiom reports. -/

#check @mathdb347302
#print Conj36Block
#check @Dissection.main
#check @Dissection.S_nonneg
#check @Drac.theoremE
#check @Drac.good_of_outer
#check @Drac.count_PD
#print axioms mathdb347302
#print axioms Dissection.main
#print axioms Dissection.S_nonneg
#print axioms Drac.theoremE
#print axioms Drac.good_of_outer
#print axioms Drac.count_PD
#print axioms Drac.inv_PD
#print axioms Checks.hex_count
#print axioms Checks.pent2_count
```
