import RCS128

/-
Copyright (c) 2026 Myeongjin Kang (review packet). Released under the MIT license.
Independent reviewer controls for the frozen RCS128 scoped support file.
Each `drop_*` theorem is the NEGATION of a frozen support statement with one
hypothesis removed or weakened, proved by an explicit counterexample.
Each `pos_*` theorem applies a frozen support theorem to concrete data, showing
the hypotheses are jointly satisfiable at the intended boundary.
No new support claim about RCS128 is made here.
-/

namespace RCS128Review
open RCS128

/-- Swap of two codes `0 ↔ 1`. -/
def swap01 (x : ℕ) : ℕ := if x = 0 then 1 else if x = 1 then 0 else x

/-- Tag swap: code `2*pos + tag`, exchanging components `T` and `rho(T)`. -/
def tagSwap (x : ℕ) : ℕ := if x % 2 = 0 then x + 1 else x - 1

/-! ### even_card_of_reflection / even_phase_card -/

theorem drop_free :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ), (∀ x ∈ s, rho x ∈ s) →
      (∀ x ∈ s, rho (rho x) = x) → Even s.card := by
  intro h
  have := h {0} id (by decide) (by decide)
  revert this; decide

theorem drop_closure :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ), (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → Even s.card := by
  intro h
  have := h {0} swap01 (by decide) (by decide)
  revert this; decide

theorem drop_involution :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ), (∀ x ∈ s, rho x ∈ s) →
      (∀ x ∈ s, rho x ≠ x) → Even s.card := by
  intro h
  have := h {0, 1, 2} (fun x => (x + 1) % 3) (by decide) (by decide)
  revert this; decide

/-- Untagged: the central occurrence of a fixed word in a reverse-complement
fixed text is its own reflection; the count is odd. -/
theorem untagged_central_occurrence_is_fixed :
    id (0 : ℕ) = 0 ∧ ¬ Even ({0} : Finset ℕ).card := by decide

/-- Tagged: the same occurrence in components `T` (code 0) and `rho(T)` (code 1)
is paired without fixed points, and the frozen theorem applies. -/
theorem pos_tagged_components : Even ({0, 1} : Finset ℕ).card :=
  even_card_of_reflection {0, 1} tagSwap (by decide) (by decide) (by decide)

theorem drop_phase_preservation :
    ¬ ∀ (s : Finset ℕ) (rho : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P],
      (∀ x ∈ s, rho x ∈ s) → (∀ x ∈ s, rho (rho x) = x) →
      (∀ x ∈ s, rho x ≠ x) → Even (s.filter P).card := by
  intro h
  have := h {0, 1} swap01 (fun x => x = 0) (by decide) (by decide) (by decide)
  revert this; decide

theorem pos_phase_card :
    Even (({0, 1, 2, 3} : Finset ℕ).filter (fun x => x < 2)).card :=
  even_phase_card {0, 1, 2, 3} tagSwap (fun x => x < 2)
    (by decide) (by decide) (by decide) (by decide)

/-! ### adjacent pairs, thresholds and the sorted bridge -/

theorem drop_downward_closure :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P], 2 * i + 1 < n →
      Even ((Finset.range n).filter P).card → (P (2 * i) ↔ P (2 * i + 1)) := by
  intro h
  have := h 3 0 (fun a => a ≠ 1) (by decide) (by decide)
  revert this; decide

theorem drop_even_tail :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P], 2 * i + 1 < n →
      (∀ a b, b < n → a ≤ b → P b → P a) → (P (2 * i) ↔ P (2 * i + 1)) := by
  intro h
  have := h 2 0 (fun a => a < 1) (by decide) (by intro a b _ hab hb; omega)
  revert this; decide

/-- Outside the listed layers the even tail says nothing (`n = 0`). -/
theorem drop_index_bound :
    ¬ ∀ (n i : ℕ) (P : ℕ → Prop) [DecidablePred P],
      (∀ a b, b < n → a ≤ b → P b → P a) →
      Even ((Finset.range n).filter P).card → (P (2 * i) ↔ P (2 * i + 1)) := by
  intro h
  have := h 0 0 (fun a => a < 1) (by intro a b hb; omega) (by decide)
  revert this; decide

/-- Exits `2,1,2` are not sorted; the phase tail `{0,2}` is even but splits pair `(0,1)`. -/
theorem drop_sortedness :
    ¬ ∀ (n i : ℕ) (z : ℕ → ℤ) (b : ℤ), 2 * i + 1 < n →
      Even ((Finset.range n).filter (fun a => b ≤ z a)).card →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h 3 0 (fun a => if a = 1 then 1 else 2) 2 (by decide) (by decide)
  revert this; decide

/-- Even TOTAL layer count instead of even PHASE count. -/
theorem drop_phase_count_for_total :
    ¬ ∀ (n i : ℕ) (z : ℕ → ℤ) (b : ℤ), 2 * i + 1 < n →
      (∀ a c, c < n → a ≤ c → z c ≤ z a) → Even n →
      (b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1)) := by
  intro h
  have := h 2 0 (fun a => if a = 0 then 2 else 1) 2 (by decide)
    (by intro a c hc hac; split_ifs <;> omega) (by decide)
  revert this; decide

/-- The bridge with exact phase-count equality replaced by TOTAL-count equality:
all reflection hypotheses hold and the conclusion fails. -/
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

/-- Concrete use of the bridge: exits `5,5,3,3`, threshold `4`, pair `(2,3)`. -/
theorem pos_bridge :
    ((4 : ℤ) ≤ (5 : ℤ) - 2 * (((2 : ℕ) / 2 : ℕ) : ℤ) ↔
      (4 : ℤ) ≤ (5 : ℤ) - 2 * (((3 : ℕ) / 2 : ℕ) : ℤ)) :=
  reflection_sorted_pair {0, 1} swap01 (fun _ => True) 4 1
    (fun a => (5 : ℤ) - 2 * ((a / 2 : ℕ) : ℤ)) 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a c _ hac; have := Nat.div_le_div_right (c := 2) hac; omega)

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

/-- Removing a "pair" one of whose members is absent from the occurrence set. -/
theorem drop_pair_present :
    ¬ ∀ (s : Finset ℕ) (a b : ℕ) (P : ℕ → Prop) [DecidablePred P],
      b ∈ s → a ≠ b → (P a ↔ P b) → Even (s.filter P).card →
      Even (((s.erase a).erase b).filter P).card := by
  intro h
  have := h {0, 1} 2 0 (fun x => x < 3) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- A present pair absent from the phase: the frozen theorem's "absent pair" branch. -/
theorem pos_pair_absent_from_phase :
    Even ((((({0, 1, 2, 3} : Finset ℕ).erase 2).erase 3)).filter (fun x => x < 2)).card :=
  even_phase_after_pair_removal {0, 1, 2, 3} 2 3 (fun x => x < 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A present pair inside the phase. -/
theorem pos_pair_present_in_phase :
    Even ((((({0, 1, 2, 3} : Finset ℕ).erase 0).erase 1)).filter (fun x => x < 2)).card :=
  even_phase_after_pair_removal {0, 1, 2, 3} 0 1 (fun x => x < 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

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
theorem odd_core_without_hk (count : ℕ → ℕ) (k : ℕ)
    (hfail : 2 * (k - 1) < count (k - 1)) : 2 * k - 1 ≤ count (k - 1) := by
  omega

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

theorem drop_budget_k :
    ¬ ∀ (k p : ℕ), 2 * ((k - 1) * p) + 2 * p = 2 * k * p := by
  intro h
  have := h 0 1
  omega

/-- At zero period the budget identity is degenerate: nothing is freed. -/
theorem zero_period_budget (k : ℕ) (hk : 1 ≤ k) :
    2 * ((k - 1) * 0) + 2 * 0 = 2 * k * 0 := odd_core_budget k 0 hk

/-- At zero period `shifted_copy_fits` is vacuous: no offset `delta < 0`. -/
theorem zero_period_shift_vacuous (delta : ℕ) : ¬ delta < 0 := Nat.not_lt_zero delta

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

/-- The bound is tight: the last copy starts at `k*p - 1` (here `p=3`, `k=2`). -/
theorem pos_shift_tight : 2 + 1 * 3 < 2 * 3 ∧ 2 + 1 * 3 = 2 * 3 - 1 :=
  ⟨shifted_copy_fits 3 2 2 1 (by decide) (by decide), by decide⟩

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

/-- The nonfixed partner case of the candidate (`(k+1) + k`) is not in the frozen
file; it is the arithmetic below, with both positive deficits at least one. -/
theorem nonfixed_partner_sum (d1 d2 k : ℕ) (h1 : 1 ≤ d1) (h2 : 1 ≤ d2) :
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

end RCS128Review
