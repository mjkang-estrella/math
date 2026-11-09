/-
# Bunkbed E7 (r5): horizontal-witness characterisation of `Bun.hor`

`Bun.hor hm R l w` is `decide` of nonemptiness of the finite attached-range filter of
indices `k ∈ Finset.range m` with `k ∈ R` and window value `w (fresH hm k · l)`.  This
module proves its exact witness characterisation: the disjunction is true iff some
`k < m` in `R` has horizontal-entry window value `w (fresH hm k hk l) = true`.

Pure logical unpacking of the existing definition in `BunState`; no new definitions,
no additional axioms.
-/
import BunReach

namespace Bun

/-- Horizontal-entry characterisation: `hor hm R l w = true` iff some `k < m` with
`k ∈ R` has horizontal-entry window value `w (fresH hm k hk l) = true`. -/
theorem hor_iff {n m : Nat} (hm : m < n) (R : Finset Nat) (l : Bool) (w : Asg n m) :
    hor hm R l w = true ↔ ∃ k : Nat, ∃ hk : k < m, k ∈ R ∧ w (fresH hm k hk l) = true := by
  unfold hor
  constructor
  · intro h
    obtain ⟨t, ht⟩ := of_decide_eq_true h
    obtain ⟨-, hc⟩ := Finset.mem_filter.mp ht
    simp at hc
    obtain ⟨hmem, hwk⟩ := hc
    exact ⟨t.1, Finset.mem_range.mp t.2, hmem, hwk⟩
  · rintro ⟨k, hk, hmem, hwk⟩
    refine decide_eq_true ⟨⟨k, Finset.mem_range.mpr hk⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp
    · rw [decide_eq_true hmem, Bool.true_and]
      exact hwk
