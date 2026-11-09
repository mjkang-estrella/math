import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

namespace ShuffleSpectrum
open Matrix

/-- Four cards drawn from the bottom, each placed on top or bottom. -/
def shuffle (choices : Fin 4 → Bool) : List (Fin 4) :=
  ([3, 2, 1, 0] : List (Fin 4)).foldl
    (fun deck card => if choices card then card :: deck else deck ++ [card]) []

/-- Position counts among all sixteen equiprobable four-coin outcomes. -/
def countMatrix : Matrix (Fin 4) (Fin 4) ℕ := fun i j =>
  (Finset.univ.filter fun choices : Fin 4 → Bool =>
    (shuffle choices)[j.val]? = some i).card

set_option maxRecDepth 10000 in
theorem counts_table : countMatrix =
    !![8, 0, 0, 8; 4, 4, 4, 4; 2, 6, 6, 2; 2, 6, 6, 2] := by
  decide

noncomputable def enumeratedProbability : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => (countMatrix i j : ℂ) / 16

/-- The source's position probabilities, with zero-based finite indices. -/
noncomputable def positionMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((Nat.choose i.val j.val : ℂ) + Nat.choose i.val (n - 1 - j.val)) /
    (2 : ℂ) ^ (i.val + 1)

theorem four_cards : positionMatrix 4 =
    !![(1:ℂ)/2, 0, 0, 1/2; 1/4, 1/4, 1/4, 1/4;
       1/8, 3/8, 3/8, 1/8; 1/8, 3/8, 3/8, 1/8] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [positionMatrix, Nat.choose]

theorem enumeration_matches_formula : enumeratedProbability = positionMatrix 4 := by
  rw [four_cards]
  ext i j
  simp only [enumeratedProbability, counts_table]
  fin_cases i <;> fin_cases j <;> norm_num

theorem no_sixteenth_vector (v : Fin 4 → ℂ)
    (h : positionMatrix 4 *ᵥ v = ((1:ℂ)/16) • v) : v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  rw [four_cards] at h0 h1 h2 h3
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
  have he0 : 7 * v 0 + 8 * v 3 = 0 := by linear_combination 16 * h0
  have he1 : 4 * v 0 + 3 * v 1 + 4 * v 2 + 4 * v 3 = 0 := by linear_combination 16 * h1
  have he2 : 2 * v 0 + 6 * v 1 + 5 * v 2 + 2 * v 3 = 0 := by linear_combination 16 * h2
  have he3 : 2 * v 0 + 6 * v 1 + 6 * v 2 + v 3 = 0 := by linear_combination 16 * h3
  have h23 : v 2 = v 3 := by linear_combination he3 - he2
  have h03 : 2 * v 0 + 3 * v 3 = 0 := by linear_combination (2 * he1 - he3 - 2 * h23) / 3
  have hz3 : v 3 = 0 := by linear_combination (7 * h03 - 2 * he0) / 5
  have hz0 : v 0 = 0 := by linear_combination (he0 - 8 * hz3) / 7
  have hz2 : v 2 = 0 := by linear_combination h23 + hz3
  have hz1 : v 1 = 0 := by linear_combination (he1 - 4 * hz0 - 4 * hz2 - 4 * hz3) / 3
  funext i
  fin_cases i <;> assumption

theorem no_sixteenth_eigenvalue :
    ¬ Module.End.HasEigenvalue (positionMatrix 4).toLin' ((1:ℂ)/16) := by
  intro h
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  exact hv.2 (no_sixteenth_vector v hv.apply_eq_smul)

theorem no_sixteenth_in_actual_shuffle :
    ¬ Module.End.HasEigenvalue enumeratedProbability.toLin' ((1:ℂ)/16) := by
  rw [enumeration_matches_formula]
  exact no_sixteenth_eigenvalue

/-- The asserted nonzero spectrum, using ceil((n-1)/2)=n/2 for natural n. -/
def SpectrumConjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ mu : ℂ,
    (mu ≠ 0 ∧ Module.End.HasEigenvalue (positionMatrix n).toLin' mu) ↔
      ∃ i : ℕ, i ≤ n / 2 ∧ mu = 1 / (2 : ℂ) ^ (2 * i)

theorem not_spectrum_conjecture : ¬ SpectrumConjecture := by
  intro h
  have hp : ∃ i : ℕ, i ≤ 4 / 2 ∧ ((1:ℂ)/16) = 1 / (2 : ℂ) ^ (2 * i) := by
    exact ⟨2, by norm_num, by norm_num⟩
  exact no_sixteenth_eigenvalue ((h 4 (by norm_num) ((1:ℂ)/16)).mpr hp).2

end ShuffleSpectrum
