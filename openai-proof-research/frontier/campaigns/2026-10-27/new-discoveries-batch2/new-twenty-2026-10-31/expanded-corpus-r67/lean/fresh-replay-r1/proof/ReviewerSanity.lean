import Clow371639.Refutation

/-! Reviewer sanity checks: the definitions are non-degenerate on the witnesses. -/

namespace Clow371639

open Finset

/-- The defining set of `χ_f` is bounded below by `0`. -/
lemma fracSet_bddBelow {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    BddBelow {r : ℝ | ∃ y : Finset V → ℝ, IsFractionalColoring G y ∧ ∑ I, y I = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨y, ⟨hy0, -, -⟩, rfl⟩
  exact sum_nonneg fun I _ => hy0 I

/-- The fractional chromatic number never exceeds the number of vertices (singleton colouring). -/
theorem fracChromaticNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : fracChromaticNumber G ≤ Fintype.card V := by
  refine (csInf_le (fracSet_bddBelow G)
    ⟨singletonWeight, isFractionalColoring_singleton G, rfl⟩).trans (le_of_eq ?_)
  unfold singletonWeight
  rw [sum_boole]
  have : (univ.filter (fun I : Finset V => I.card = 1)) =
      univ.map ⟨fun v => ({v} : Finset V), fun a b h => singleton_injective h⟩ := by
    ext I
    simp only [mem_filter, mem_univ, true_and, mem_map, card_eq_one]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  simp [this]

/-- The fractional chromatic number is nonnegative. -/
theorem fracChromaticNumber_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : 0 ≤ fracChromaticNumber G := by
  refine le_csInf (fracSet_nonempty G) ?_
  rintro r ⟨y, ⟨hy0, -, -⟩, rfl⟩
  exact sum_nonneg fun I _ => hy0 I

/-- Sanity: the five-cycle adjacency is the expected one. -/
example : c5Adj 0 1 ∧ c5Adj 1 2 ∧ c5Adj 2 3 ∧ c5Adj 3 4 ∧ c5Adj 4 0 ∧ ¬ c5Adj 0 2 := by decide

/-- Sanity: `C₅` has an independent set and a clique of size `2`, so the bounds `≤ 2` are tight. -/
example : ∃ T : Finset (Fin 5), (∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ c5Adj a b) ∧ T.card = 2 :=
  ⟨{0, 2}, by decide, by decide⟩

example : ∃ T : Finset (Fin 5), (∀ a ∈ T, ∀ b ∈ T, a ≠ b → c5Adj a b) ∧ T.card = 2 :=
  ⟨{0, 1}, by decide, by decide⟩

/-- Sanity: the witness for `k = 1` has `χ > ω`, and `χ_f ≥ 5 / 2`. -/
example : ((padGraph 1).cliqueNum : ℕ∞) < (padGraph 1).chromaticNumber :=
  pad_cliqueNum_lt_chromaticNumber 1 le_rfl

example : (5 / 2 : ℝ) ≤ fracChromaticNumber (padGraph 1) := by
  simpa using pad_frac_ge 1

end Clow371639
