import RCS128

/-
Copyright (c) 2026 Myeongjin Kang (review packet). Released under the MIT license.
Independent reviewer controls for the frozen RCS128 scoped support file (review r2).

Provenance: many statements were first drafted in the interrupted r1 review
(`../../rcs128-formal-review-r1/checks/ReviewerControls.lean`, unverified when r1
was killed). Each was re-read, corrected or replaced in r2, and only this file is
compiled as evidence.

* `drop_*`: the NEGATION of a frozen support statement with one hypothesis removed
  or weakened, proved by an explicit finite counterexample.
* `pos_*`: an application of a frozen theorem to concrete data, showing that its
  hypotheses can all hold at once at the named boundary.
* `note_*`: a remark about what a frozen statement does or does not cover.
No new support claim about RCS128 is made here.
-/

namespace RCS128Review
open RCS128

/-- Swap of the two codes `0 ↔ 1`, identity elsewhere. -/
def swap01 (x : ℕ) : ℕ := if x = 0 then 1 else if x = 1 then 0 else x

/-- Tagged reflection on codes `2*pos + tag`: exchanges component `T` (tag 0) with
component `rho(T)` (tag 1) at the same position. -/
def tagSwap (x : ℕ) : ℕ := if x % 2 = 0 then x + 1 else x - 1

/-- Antitone exits `5,5,3,3,1,1,…` used for the positive bridge controls. -/
def zEx (a : ℕ) : ℤ := 5 - 2 * ((a / 2 : ℕ) : ℤ)

theorem zEx_antitone : ∀ a c, c < 4 → a ≤ c → zEx c ≤ zEx a := by
  intro a c _ hac
  have := Nat.div_le_div_right (c := 2) hac
  unfold zEx
  omega

/-! ### even_card_of_reflection / even_phase_card -/

/-- Fixed-point-free hypothesis dropped: a reflection fixing its only occurrence. -/
theorem drop_free :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ), (∀ x ∈ s, rho x ∈ s) →
      (∀ x ∈ s, rho (rho x) = x) → Even s.card := by
  intro h
  have := h {0} id (by decide) (by decide)
  revert this; decide

/-- Closure dropped: the partner of the only occurrence lies outside the set. -/
theorem drop_closure :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ), (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → Even s.card := by
  intro h
  have := h {0} swap01 (by decide) (by decide)
  revert this; decide

/-- Involution dropped: a fixed-point-free 3-cycle. -/
theorem drop_involution :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ), (∀ x ∈ s, rho x ∈ s) →
      (∀ x ∈ s, rho x ≠ x) → Even s.card := by
  intro h
  have := h {0, 1, 2} (fun x => (x + 1) % 3) (by decide) (by decide)
  revert this; decide

/-- Untagged single text: the central occurrence of a fixed word in a
reflection-fixed text is its own reflection, and the count is odd. -/
theorem note_untagged_central_occurrence_is_fixed :
    id (0 : ℕ) = 0 ∧ ¬ Even ({0} : Finset ℕ).card := by decide

/-- Tagged components: the same occurrence in `T` (code 0) and `rho(T)` (code 1)
is paired without fixed points, so the frozen theorem applies. -/
theorem pos_tagged_components : Even ({0, 1} : Finset ℕ).card :=
  even_card_of_reflection {0, 1} tagSwap (by decide) (by decide) (by decide)

/-- Phase preservation dropped: the total count is even (2) but the phase count is 1. -/
theorem drop_phase_preservation :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P],
      (∀ x ∈ s, rho x ∈ s) → (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → Even (s.filter P).card := by
  intro h
  have := h {0, 1} swap01 (fun x => x = 0) (by decide) (by decide) (by decide)
  revert this; decide

/-- Even total occurrence count does not give an even phase count, even for a
genuine fixed-point-free involution. -/
theorem drop_phase_total_parity :
    Even ({0, 1} : Finset ℕ).card ∧
      ¬ Even (({0, 1} : Finset ℕ).filter (fun x => x = 0)).card := by decide

theorem pos_phase_card :
    Even (({0, 1, 2, 3} : Finset ℕ).filter (fun x => x < 2)).card :=
  even_phase_card {0, 1, 2, 3} tagSwap (fun x => x < 2)
    (by decide) (by decide) (by decide) (by decide)

/-! ### adjacent pairs, thresholds and the sorted bridge -/

/-- Downward closure dropped: phase set `{0,2}` of three layers is even but splits pair `(0,1)`. -/
theorem drop_downward_closure :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P], 2 * i + 1 < n →
      Even ((Finset.range n).filter P).card → (P (2 * i) ↔ P (2 * i + 1)) := by
  intro h
  have := h 3 0 (fun a => a ≠ 1) (by decide) (by decide)
  revert this; decide

/-- Even tail dropped: an odd initial segment ends inside the first pair. -/
theorem drop_even_tail :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P], 2 * i + 1 < n →
      (∀ a b, b < n → a ≤ b → P b → P a) → (P (2 * i) ↔ P (2 * i + 1)) := by
  intro h
  have := h 2 0 (fun a => a < 1) (by decide) (by intro a b _ hab hb; omega)
  revert this; decide

/-- Pairing must start at the top: offset pairs `(2i+1, 2i+2)` are not controlled. -/
theorem drop_pair_offset :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P], 2 * i + 2 < n →
      (∀ a b, b < n → a ≤ b → P b → P a) →
      Even ((Finset.range n).filter P).card → (P (2 * i + 1) ↔ P (2 * i + 2)) := by
  intro h
  have := h 3 0 (fun a => a < 2) (by decide)
    (by intro a b _ hab hb; omega) (by decide)
  revert this; decide

/-- Index bound dropped: outside the listed layers (`n = 0`) the even tail says nothing. -/
theorem drop_index_bound :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P],
      (∀ a b, b < n → a ≤ b → P b → P a) →
      Even ((Finset.range n).filter P).card → (P (2 * i) ↔ P (2 * i + 1)) := by
  intro h
  have := h 0 0 (fun a => a < 1) (by intro a b hb; omega) (by decide)
  revert this; decide

/-- Sortedness dropped: exits `2,1,2` at threshold `2` give an even tail that splits pair `(0,1)`. -/
theorem drop_sortedness :
    ¬ ∀ (n i : ℕ) (z : ℕ → ℤ) (b : ℤ), 2 * i + 1 < n →
      Even ((Finset.range n).filter (fun a => b ≤ z a)).card →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h 3 0 (fun a => if a = 1 then 1 else 2) 2 (by decide) (by decide)
  revert this; decide

/-- Even TOTAL layer count in place of even PHASE count. -/
theorem drop_phase_count_for_total :
    ¬ ∀ (n i : ℕ) (z : ℕ → ℤ) (b : ℤ), 2 * i + 1 < n →
      (∀ a c, c < n → a ≤ c → z c ≤ z a) → Even n →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h 2 0 (fun a => if a = 0 then 2 else 1) 2 (by decide)
    (by intro a c hc hac; split_ifs <;> omega) (by decide)
  revert this; decide

/-- Bridge with exact PHASE-count equality replaced by TOTAL-count equality: every
reflection hypothesis holds and the conclusion fails. -/
theorem drop_bridge_total_count :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
      (n i : ℕ) (z : ℕ → ℤ) (b : ℤ),
      (∀ x ∈ s, rho x ∈ s) → (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → (∀ x ∈ s, P x → P (rho x)) →
      s.card = n → 2 * i + 1 < n → (∀ a c, c < n → a ≤ c → z c ≤ z a) →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h {0, 1} swap01 (fun _ => True) 2 0 (fun a => if a = 0 then 2 else 1) 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a c hc hac; split_ifs <;> omega)
  revert this; decide

/-- One-sided count transfer `≤` is insufficient (empty occurrence set). -/
theorem drop_bridge_count_le :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
      (n i : ℕ) (z : ℕ → ℤ) (b : ℤ),
      (∀ x ∈ s, rho x ∈ s) → (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → (∀ x ∈ s, P x → P (rho x)) →
      (s.filter P).card ≤ ((Finset.range n).filter (fun a => b ≤ z a)).card →
      2 * i + 1 < n → (∀ a c, c < n → a ≤ c → z c ≤ z a) →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h ∅ id (fun _ => True) 2 0 (fun a => if a = 0 then 2 else 1) 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a c hc hac; split_ifs <;> omega)
  revert this; decide

/-- One-sided count transfer `≥` is insufficient. -/
theorem drop_bridge_count_ge :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
      (n i : ℕ) (z : ℕ → ℤ) (b : ℤ),
      (∀ x ∈ s, rho x ∈ s) → (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → (∀ x ∈ s, P x → P (rho x)) →
      ((Finset.range n).filter (fun a => b ≤ z a)).card ≤ (s.filter P).card →
      2 * i + 1 < n → (∀ a c, c < n → a ≤ c → z c ≤ z a) →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h {0, 1} swap01 (fun _ => True) 2 0 (fun a => if a = 0 then 2 else 1) 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a c hc hac; split_ifs <;> omega)
  revert this; decide

/-- Bridge applied to exits `5,5,3,3`, threshold `4`: pair `(2,3)` (both below). -/
theorem pos_bridge_lower :
    ((4 : ℤ) ≤ zEx (2 * 1) ↔ (4 : ℤ) ≤ zEx (2 * 1 + 1)) :=
  reflection_sorted_pair {0, 1} swap01 (fun _ => True) 4 1 zEx 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) zEx_antitone

/-- Same data, pair `(0,1)` (both at or above the threshold). -/
theorem pos_bridge_upper :
    ((4 : ℤ) ≤ zEx (2 * 0) ↔ (4 : ℤ) ≤ zEx (2 * 0 + 1)) ∧ (4 : ℤ) ≤ zEx 0 :=
  ⟨reflection_sorted_pair {0, 1} swap01 (fun _ => True) 4 0 zEx 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) zEx_antitone,
   by decide⟩

/-! ### pair removal -/

theorem drop_erase_member :
    ¬ ∀ (s : Finset ℕ) (a b : ℕ), b ∈ s → a ≠ b → Even s.card →
      Even ((s.erase a).erase b).card := by
  intro h
  have := h {0, 1} 2 0 (by decide) (by decide) (by decide)
  revert this; decide

theorem drop_erase_distinct :
    ¬ ∀ (s : Finset ℕ) (a b : ℕ), a ∈ s → b ∈ s → Even s.card →
      Even ((s.erase a).erase b).card := by
  intro h
  have := h {0, 1} 0 0 (by decide) (by decide) (by decide)
  revert this; decide

/-- Pair members disagreeing at the phase. -/
theorem drop_pair_agreement :
    ¬ ∀ (s : Finset ℕ) (a b : ℕ) (P : ℕ → Prop) [DecidablePred P],
      a ∈ s → b ∈ s → a ≠ b → Even (s.filter P).card →
      Even (((s.erase a).erase b).filter P).card := by
  intro h
  have := h {0, 1, 2} 1 2 (fun x => x < 2) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- A "pair" with one member absent from the occurrence set (agreement still holds). -/
theorem drop_pair_present :
    ¬ ∀ (s : Finset ℕ) (a b : ℕ) (P : ℕ → Prop) [DecidablePred P],
      b ∈ s → a ≠ b → (P a ↔ P b) → Even (s.filter P).card →
      Even (((s.erase a).erase b).filter P).card := by
  intro h
  have := h {0, 1} 2 0 (fun x => x < 3) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- A present pair absent from the phase: the frozen theorem's `¬ P a` branch. -/
theorem pos_pair_absent_from_phase :
    Even ((({0, 1, 2, 3} : Finset ℕ).erase 2).erase 3 |>.filter (fun x => x < 2)).card :=
  even_phase_after_pair_removal {0, 1, 2, 3} 2 3 (fun x => x < 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A present pair inside the phase. -/
theorem pos_pair_present_in_phase :
    Even ((({0, 1, 2, 3} : Finset ℕ).erase 0).erase 1 |>.filter (fun x => x < 2)).card :=
  even_phase_after_pair_removal {0, 1, 2, 3} 0 1 (fun x => x < 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Both members absent from `s`: true trivially, but NOT an instance of the frozen
theorem (which requires membership). Recorded so "absent pairs" in the frozen
docstring is read as "absent from the phase". -/
theorem note_both_absent_trivial (s : Finset ℕ) (a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (ha : a ∉ s) (hb : b ∉ s) (heven : Even (s.filter P).card) :
    Even (((s.erase a).erase b).filter P).card := by
  rw [Finset.erase_eq_of_notMem ha, Finset.erase_eq_of_notMem hb]
  exact heven

/-! ### entry/exit visitation -/

theorem drop_entry_order :
    ¬ ∀ (upperEntry lowerEntry upperExit lowerExit b : ℤ),
      (upperEntry ≤ b ∧ b ≤ upperExit) → (b ≤ upperExit ↔ b ≤ lowerExit) →
      lowerEntry ≤ b ∧ b ≤ lowerExit := by
  intro h
  have := h 0 1 0 0 0 (by decide) (by decide)
  revert this; decide

theorem drop_tail_agreement :
    ¬ ∀ (upperEntry lowerEntry upperExit lowerExit b : ℤ),
      lowerEntry ≤ upperEntry → (upperEntry ≤ b ∧ b ≤ upperExit) →
      lowerEntry ≤ b ∧ b ≤ lowerExit := by
  intro h
  have := h 0 0 0 (-1) 0 (by decide) (by decide)
  revert this; decide

/-! ### first-success threshold, odd core, records -/

/-- The hypothesis `1 < k` of `odd_core_from_previous_failure` is not needed. -/
theorem note_odd_core_without_hk (count : ℕ → ℕ) (k : ℕ)
    (hfail : 2 * (k - 1) < count (k - 1)) : 2 * k - 1 ≤ count (k - 1) := by
  omega

/-- Tight boundary: a previous failure by exactly one layer gives exactly `2k-1`. -/
theorem pos_odd_core_tight : 2 * 2 - 1 ≤ (fun _ : ℕ => 3) (2 - 1) ∧ (fun _ : ℕ => 3) (2 - 1) = 2 * 2 - 1 :=
  ⟨odd_core_from_previous_failure (fun _ => 3) 2 (by decide) (by decide), rfl⟩

/-- `r = 0` cannot be the bounded endpoint. -/
theorem drop_first_threshold_start :
    ¬ ∀ (count : ℕ → ℕ) (r : ℕ), count r ≤ 2 * r →
      ∃ k, 1 ≤ k ∧ k ≤ r ∧ count k ≤ 2 * k ∧ (k = 1 ∨ 2 * k - 1 ≤ count (k - 1)) := by
  intro h
  obtain ⟨k, hk1, hkr, -⟩ := h (fun _ => 0) 0 (by decide)
  omega

/-- At `k = 1` there is no previous failure; the disjunct `k = 1` cannot be dropped. -/
theorem drop_k_one_branch :
    ¬ ∀ (count : ℕ → ℕ) (r : ℕ), 1 ≤ r → count r ≤ 2 * r →
      ∃ k, 1 ≤ k ∧ k ≤ r ∧ count k ≤ 2 * k ∧ 2 * k - 1 ≤ count (k - 1) := by
  intro h
  obtain ⟨k, hk1, hkr, -, hcore⟩ := h (fun _ => 0) 1 (by decide) (by decide)
  omega

/-- `k = 1` boundary of the frozen threshold theorem at `r = 1`. -/
theorem pos_first_threshold_k_one :
    ∃ k, 1 ≤ k ∧ k ≤ 1 ∧ (fun _ : ℕ => 2) k ≤ 2 * k ∧
      (k = 1 ∨ 2 * k - 1 ≤ (fun _ : ℕ => 2) (k - 1)) :=
  first_threshold_core (fun _ => 2) 1 (by decide) (by decide)

/-- The frozen threshold theorem with counts `5,5,5,6`: any returned `k` is `3`,
and it carries the odd core `5 = 2*3-1`. -/
def cnt (k : ℕ) : ℕ := if k < 3 then 5 else 6

theorem pos_first_threshold_k_three :
    ∃ k, 1 ≤ k ∧ k ≤ 3 ∧ cnt k ≤ 2 * k ∧ (k = 1 ∨ 2 * k - 1 ≤ cnt (k - 1)) :=
  first_threshold_core cnt 3 (by decide) (by decide)

theorem note_threshold_k_three_forced (k : ℕ) (h1 : 1 ≤ k) (h3 : k ≤ 3)
    (hc : cnt k ≤ 2 * k) : k = 3 := by
  unfold cnt at hc; split_ifs at hc <;> omega

/-- Exactly `2*k` records can all be identical alignments. -/
theorem drop_surplus_to_2k :
    ¬ ∀ (records identical : Finset ℕ) (k : ℕ), 2 * k ≤ records.card →
      identical.card ≤ 2 * k → ∃ x ∈ records, x ∉ identical := by
  intro h
  have := h (Finset.range 2) (Finset.range 2) 1 (by decide) (by decide)
  revert this; decide

theorem drop_alignment_cap :
    ¬ ∀ (records identical : Finset ℕ) (k : ℕ), 2 * k + 1 ≤ records.card →
      ∃ x ∈ records, x ∉ identical := by
  intro h
  have := h (Finset.range 3) (Finset.range 3) 1 (by decide)
  revert this; decide

theorem pos_record_outside :
    ∃ x ∈ Finset.range 3, x ∉ Finset.range 2 :=
  exists_record_outside_alignment (Finset.range 3) (Finset.range 2) 1 (by decide) (by decide)

/-- `k = 0`: a single record with an empty identical-alignment set. -/
theorem pos_record_outside_k_zero : ∃ x ∈ Finset.range 1, x ∉ (∅ : Finset ℕ) :=
  exists_record_outside_alignment (Finset.range 1) ∅ 0 (by decide) (by decide)

theorem drop_budget_k :
    ¬ ∀ (k p : ℕ), 2 * ((k - 1) * p) + 2 * p = 2 * k * p := by
  intro h
  have := h 0 1
  omega

/-- At zero period the budget identity is degenerate: nothing is freed. -/
theorem pos_zero_period_budget (k : ℕ) (hk : 1 ≤ k) :
    2 * ((k - 1) * 0) + 2 * 0 = 2 * k * 0 := odd_core_budget k 0 hk

/-- At zero period `shifted_copy_fits` is vacuous: there is no offset `delta < 0`. -/
theorem note_zero_period_shift_vacuous (delta : ℕ) : ¬ delta < 0 := Nat.not_lt_zero delta

theorem drop_shift_offset :
    ¬ ∀ (p k delta j : ℕ), j < k → delta + j * p < k * p := by
  intro h
  have := h 1 1 1 0 (by decide)
  omega

theorem drop_shift_index :
    ¬ ∀ (p k delta j : ℕ), delta < p → delta + j * p < k * p := by
  intro h
  have := h 1 1 0 1 (by decide)
  omega

/-- Tight: the last copy starts at `k*p - 1` (here `p = 3`, `k = 2`). -/
theorem pos_shift_tight : 2 + 1 * 3 < 2 * 3 ∧ 2 + 1 * 3 = 2 * 3 - 1 :=
  ⟨shifted_copy_fits 3 2 2 1 (by decide) (by decide), by decide⟩

/-- `k = 1`: the single shifted copy at any offset `delta < p`. -/
theorem pos_shift_k_one : 4 + 0 * 5 < 1 * 5 :=
  shifted_copy_fits 5 1 4 0 (by decide) (by decide)

/-! ### fixed-word deficit and final accounting -/

theorem drop_deficit_even :
    ¬ ∀ (delta k : ℕ), 0 < delta → 2 * k + 1 ≤ delta * (k + 1) := by
  intro h
  have := h 1 1 (by decide)
  omega

theorem drop_deficit_positive :
    ¬ ∀ (delta k : ℕ), Even delta → 2 * k + 1 ≤ delta * (k + 1) := by
  intro h
  have := h 0 0 (by decide)
  omega

/-- Smallest positive even deficit at `k = 1`: `3 ≤ 4`. -/
theorem pos_deficit_two : 2 * 1 + 1 ≤ 2 * (1 + 1) :=
  fixed_deficit_surplus 2 1 (by decide) (by decide)

/-- The candidate's NONFIXED partner case (`(k+1) + k`, both deficits positive) is
not in the frozen file; it is this reviewer arithmetic. -/
theorem note_nonfixed_partner_sum (d1 d2 k : ℕ) (h1 : 1 ≤ d1) (h2 : 1 ≤ d2) :
    2 * k + 1 ≤ d1 * (k + 1) + d2 * k := by
  nlinarith

theorem drop_half :
    ¬ ∀ (output upCost weight optimum : ℕ), output = upCost →
      upCost ≤ 2 * weight → weight ≤ 2 * optimum → output ≤ 2 * optimum := by
  intro h
  have := h 4 4 2 1 rfl (by decide) (by decide)
  omega

theorem drop_connection :
    ¬ ∀ (output upCost weight optimum : ℕ), 2 * output = upCost →
      weight ≤ 2 * optimum → output ≤ 2 * optimum := by
  intro h
  have := h 3 6 1 1 rfl (by decide)
  omega

theorem drop_lower_bound :
    ¬ ∀ (output upCost weight optimum : ℕ), 2 * output = upCost →
      upCost ≤ 2 * weight → output ≤ 2 * optimum := by
  intro h
  have := h 2 4 2 0 rfl (by decide)
  omega

/-- Empty input boundary: everything zero. -/
theorem pos_final_empty : 0 ≤ 2 * 0 := final_length_bound 0 0 0 0 rfl le_rfl le_rfl

end RCS128Review
