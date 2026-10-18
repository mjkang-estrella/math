import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-
Copyright (c) 2026 Myeongjin Kang. Released under the MIT license.
Scoped finite combinatorial support for RCS128, not a formalization of the
superstring algorithm. Phase occurrences, reflection and sorted-layer identities
must still be constructed in the mathematical proof.
-/

namespace RCS128

/-- A finite occurrence set paired by a fixed-point-free reflection has even size. -/
theorem even_card_of_reflection (s : Finset ℕ) (rho : ℕ → ℕ)
    (hclosed : ∀ x ∈ s, rho x ∈ s)
    (hinv : ∀ x ∈ s, rho (rho x) = x)
    (hfree : ∀ x ∈ s, rho x ≠ x) : Even s.card := by
  have hcard : (s.filter (fun x => x < rho x)).card =
      (s.filter (fun x => ¬ x < rho x)).card := by
    apply Finset.card_bij (fun x _ => rho x)
    · intro x hx
      obtain ⟨hxs, hlt⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hclosed x hxs, ?_⟩
      rw [hinv x hxs]
      omega
    · intro x hx y hy hxy
      have hxs := (Finset.mem_filter.mp hx).1
      have hys := (Finset.mem_filter.mp hy).1
      calc x = rho (rho x) := (hinv x hxs).symm
           _ = rho (rho y) := congrArg rho hxy
           _ = y := hinv y hys
    · intro y hy
      obtain ⟨hys, hnot⟩ := Finset.mem_filter.mp hy
      have hne := hfree y hys
      refine ⟨rho y, ?_, hinv y hys⟩
      apply Finset.mem_filter.mpr
      refine ⟨hclosed y hys, ?_⟩
      rw [hinv y hys]
      omega
  refine ⟨(s.filter (fun x => x < rho x)).card, ?_⟩
  have hsum := Finset.card_filter_add_card_filter_not (s := s) (fun x => x < rho x)
  omega

/-- Parity of a phase predicate follows from an actual reflection on its occurrences. -/
theorem even_phase_card (s : Finset ℕ) (rho : ℕ → ℕ) (P : ℕ → Prop)
    [DecidablePred P]
    (hclosed : ∀ x ∈ s, rho x ∈ s)
    (hinv : ∀ x ∈ s, rho (rho x) = x)
    (hfree : ∀ x ∈ s, rho x ≠ x)
    (hphase : ∀ x ∈ s, P x → P (rho x)) :
    Even (s.filter P).card := by
  apply even_card_of_reflection (s.filter P) rho
  · intro x hx
    obtain ⟨hxs, hp⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hclosed x hxs, hphase x hxs hp⟩
  · intro x hx
    exact hinv x (Finset.mem_filter.mp hx).1
  · intro x hx
    exact hfree x (Finset.mem_filter.mp hx).1

/-- An initial segment with a change between positions `j` and `j+1`. -/
theorem filter_eq_range_at_boundary (n j : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hj : j + 1 < n)
    (hdown : ∀ a b, b < n → a ≤ b → P b → P a)
    (hyes : P j) (hno : ¬ P (j + 1)) :
    (Finset.range n).filter P = Finset.range (j + 1) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨han, ha⟩
    by_contra h
    have hja : j + 1 ≤ a := by omega
    exact hno (hdown (j + 1) a han hja ha)
  · intro ha
    exact ⟨by omega, hdown a j (by omega) (by omega) hyes⟩

/-- Even phase-tail cardinality forces each adjacent pair to agree at that phase. -/
theorem adjacent_pair_of_even_tail (n i : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hi : 2 * i + 1 < n)
    (hdown : ∀ a b, b < n → a ≤ b → P b → P a)
    (heven : Even ((Finset.range n).filter P).card) :
    P (2 * i) ↔ P (2 * i + 1) := by
  constructor
  · intro hyes
    by_contra hno
    have hset := filter_eq_range_at_boundary n (2 * i) P hi hdown hyes hno
    rw [hset, Finset.card_range] at heven
    obtain ⟨k, hk⟩ := heven
    omega
  · exact hdown (2 * i) (2 * i + 1) hi (by omega)

/-- The layer predicate is a threshold on antitone exit endpoints. -/
theorem adjacent_exit_threshold (n i : ℕ) (z : ℕ → ℤ) (b : ℤ)
    (hi : 2 * i + 1 < n)
    (hz : ∀ a c, c < n → a ≤ c → z c ≤ z a)
    (heven : Even ((Finset.range n).filter (fun a => b ≤ z a)).card) :
    b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1) := by
  apply adjacent_pair_of_even_tail n i (fun a => b ≤ z a) hi
  · intro a c hcn hac hb
    exact hb.trans (hz a c hcn hac)
  · exact heven

/-- The occurrence-to-sorted-tail bridge uses preservation of the phase count. -/
theorem reflection_sorted_pair (s : Finset ℕ) (rho : ℕ → ℕ)
    (P : ℕ → Prop) [DecidablePred P] (n i : ℕ) (z : ℕ → ℤ) (b : ℤ)
    (hclosed : ∀ x ∈ s, rho x ∈ s)
    (hinv : ∀ x ∈ s, rho (rho x) = x)
    (hfree : ∀ x ∈ s, rho x ≠ x)
    (hphase : ∀ x ∈ s, P x → P (rho x))
    (hcount : (s.filter P).card =
      ((Finset.range n).filter (fun a => b ≤ z a)).card)
    (hi : 2 * i + 1 < n)
    (hz : ∀ a c, c < n → a ≤ c → z c ≤ z a) :
    b ≤ z (2 * i) ↔ b ≤ z (2 * i + 1) := by
  apply adjacent_exit_threshold n i z b hi hz
  rw [← hcount]
  exact even_phase_card s rho P hclosed hinv hfree hphase

/-- Removing two distinct members preserves parity of a finite tail. -/
theorem even_card_erase_pair (s : Finset ℕ) (a b : ℕ)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (heven : Even s.card) :
    Even ((s.erase a).erase b).card := by
  have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb'
  obtain ⟨k, hk⟩ := heven
  refine ⟨k - 1, ?_⟩
  omega

/-- Removing a complete pair preserves each phase tail, including absent pairs. -/
theorem even_phase_after_pair_removal (s : Finset ℕ) (a b : ℕ)
    (P : ℕ → Prop) [DecidablePred P]
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hpair : P a ↔ P b) (heven : Even (s.filter P).card) :
    Even (((s.erase a).erase b).filter P).card := by
  have heq : ((s.erase a).erase b).filter P = ((s.filter P).erase a).erase b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [heq]
  by_cases hpa : P a
  · apply even_card_erase_pair (s.filter P) a b
    · exact Finset.mem_filter.mpr ⟨ha, hpa⟩
    · exact Finset.mem_filter.mpr ⟨hb, hpair.mp hpa⟩
    · exact hab
    · exact heven
  · have hpb : ¬ P b := fun h => hpa (hpair.mpr h)
    simpa [Finset.erase_eq_of_notMem, hpa, hpb] using heven

/-- Shared entry/exit inequalities turn a recorded word into a visited vertex. -/
theorem lower_pair_visits_axis (upperEntry lowerEntry upperExit lowerExit b : ℤ)
    (hentry : lowerEntry ≤ upperEntry)
    (hupper : upperEntry ≤ b ∧ b ≤ upperExit)
    (htail : b ≤ upperExit ↔ b ≤ lowerExit) :
    lowerEntry ≤ b ∧ b ≤ lowerExit :=
  ⟨hentry.trans hupper.1, htail.mp hupper.2⟩

/-- A first successful positive threshold retains a core of `2*k-1` layers. -/
theorem odd_core_from_previous_failure (count : ℕ → ℕ) (k : ℕ)
    (hk : 1 < k) (hfail : 2 * (k - 1) < count (k - 1)) :
    2 * k - 1 ≤ count (k - 1) := by
  omega

/-- A bounded successful endpoint makes the first-success search terminate. -/
theorem first_threshold_core (count : ℕ → ℕ) (r : ℕ)
    (hr : 1 ≤ r) (hend : count r ≤ 2 * r) :
    ∃ k, 1 ≤ k ∧ k ≤ r ∧ count k ≤ 2 * k ∧
      (k = 1 ∨ 2 * k - 1 ≤ count (k - 1)) := by
  have hex : ∃ k, 1 ≤ k ∧ count k ≤ 2 * k := ⟨r, hr, hend⟩
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkr : k ≤ r := Nat.find_min' hex ⟨hr, hend⟩
  refine ⟨k, hk.1, hkr, hk.2, ?_⟩
  by_cases h : k = 1
  · exact Or.inl h
  · right
    have hpos : 1 < k := by omega
    have hfail : ¬ (1 ≤ k - 1 ∧ count (k - 1) ≤ 2 * (k - 1)) :=
      Nat.find_min hex (show k - 1 < k by omega)
    have hf : 2 * (k - 1) < count (k - 1) := by omega
    exact odd_core_from_previous_failure count k hpos hf

/-- The strengthened surplus forces a record outside the identical-alignment set. -/
theorem exists_record_outside_alignment {α : Type*} [DecidableEq α]
    (records identical : Finset α) (k : ℕ)
    (hsurplus : 2 * k + 1 ≤ records.card)
    (hcap : identical.card ≤ 2 * k) :
    ∃ x ∈ records, x ∉ identical := by
  by_contra h
  have hsub : records ⊆ identical := by
    intro x hx
    by_contra hn
    exact h ⟨x, hx, hn⟩
  have hcard := Finset.card_le_card hsub
  omega

/-- Internal joining of the odd core leaves a whole mirrored period available. -/
theorem odd_core_budget (k p : ℕ) (hk : 1 ≤ k) :
    2 * ((k - 1) * p) + 2 * p = 2 * k * p := by
  have h : k - 1 + 1 = k := by omega
  nlinarith

/-- The shifted reflected copies fit even when the displayed period is not least. -/
theorem shifted_copy_fits (p k delta j : ℕ)
    (hdelta : delta < p) (hj : j < k) :
    delta + j * p < k * p := by
  have hmul : (j + 1) * p ≤ k * p := Nat.mul_le_mul_right p (by omega)
  nlinarith

/-- A positive even deficit at a fixed word contributes two copies or more. -/
theorem fixed_deficit_surplus (delta k : ℕ) (hpos : 0 < delta)
    (heven : Even delta) :
    2 * k + 1 ≤ delta * (k + 1) := by
  obtain ⟨d, hd⟩ := heven
  have : 2 ≤ delta := by omega
  nlinarith

/-- This is the candidate's final factor accounting, conditional on its graph bounds. -/
theorem final_length_bound (output upCost weight optimum : ℕ)
    (hhalf : 2 * output = upCost)
    (hconnection : upCost ≤ 2 * weight)
    (hcount : weight ≤ 2 * optimum) :
    output ≤ 2 * optimum := by
  omega

end RCS128
