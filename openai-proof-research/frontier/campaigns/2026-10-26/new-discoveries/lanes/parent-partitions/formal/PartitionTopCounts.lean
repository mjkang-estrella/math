import Mathlib

namespace KeithMulticolor

/-- Number of distinct missing-size pairs with given sum. -/
def missingPairCount (N s : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (N + 1),
    if 1 ≤ a ∧ a < s - a ∧ s - a ≤ N then 1 else 0

/-- The finite combinatorial sum from the missing/repeated-size classification.
The bridge from this sum to literal box partitions remains to be formalized. -/
def twoMissingSum (N : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (2 * N + 1),
    let m := missingPairCount N s
    m * (m - 1 + (if s % 2 = 0 then 1 else 0) + (if s ≤ N then 1 else 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem twoMissingSum_twentyfive : twoMissingSum 25 = 2444 := by
  decide +kernel

/-- The three coefficient formulas after substituting the top distinct-size counts.
This model is not yet a formal definition of the source's entire array. -/
def topCutValues (N : ℕ) : Fin 3 → ℕ
  | 0 => N.choose 5
  | 1 => N * (N - 1).choose 3
  | 2 => (N - 2) * twoMissingSum N + N * (N - 1) * (N - 2) / 2

theorem topCutValues_twentyfive :
    topCutValues 25 0 = 53130 ∧ topCutValues 25 1 = 50600 ∧
      topCutValues 25 2 = 63112 := by
  norm_num [topCutValues, twoMissingSum_twentyfive, Nat.choose]

theorem topCutValues_strict_valley :
    topCutValues 25 1 < topCutValues 25 0 ∧
      topCutValues 25 1 < topCutValues 25 2 := by
  obtain ⟨h₀, h₁, h₂⟩ := topCutValues_twentyfive
  omega

/-- Ordinary weak unimodality on a finite ordered index set. -/
def Unimodal {n : ℕ} (f : Fin n → ℕ) : Prop :=
  ∃ peak : Fin n,
    (∀ i j, i ≤ j → j ≤ peak → f i ≤ f j) ∧
    (∀ i j, peak ≤ i → i ≤ j → f j ≤ f i)

theorem strict_valley_not_unimodal (f : Fin 3 → ℕ)
    (h₀ : f 1 < f 0) (h₂ : f 1 < f 2) : ¬ Unimodal f := by
  rintro ⟨peak, hleft, hright⟩
  by_cases hp : (1 : Fin 3) ≤ peak
  · have := hleft 0 1 (by decide) hp
    omega
  · have hp' : peak ≤ (1 : Fin 3) := le_of_not_ge hp
    have := hright 1 2 hp' (by decide)
    omega

theorem topCutValues_not_unimodal : ¬ Unimodal (topCutValues 25) := by
  obtain ⟨h₀, h₂⟩ := topCutValues_strict_valley
  exact strict_valley_not_unimodal _ h₀ h₂

end KeithMulticolor
