import UpperCoverage
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open scoped BigOperators
namespace WheelFormal
attribute [local instance] Classical.propDecidable
abbrev ColourIndex (t : ℕ) := ZMod (2*t+1) ⊕
  ((ZMod (2*t+1) × (ZMod (2*t+1) × Fin 2)) ⊕ (ZMod (2*t+1) × ZMod (2*t+1)))
noncomputable abbrev colourSets (t : ℕ) : ColourIndex t →
    {s : WheelSet t // Independent (wheelSquare t) s}
  | .inl s => ⟨family0 t s,family0_independent t s⟩
  | .inr (.inl (a,b,c)) => ⟨family1 t a b c,family1_independent t a b c⟩
  | .inr (.inr (a,b)) => ⟨family2 t a b,family2_independent t a b⟩
noncomputable def colourWeights (t : ℕ) : ColourIndex t → ℝ
  | .inl _ => 1/(2*(t:ℝ)+1)
  | .inr (.inl _) => 1/(2*(2*(t:ℝ)+1)*(2*(t:ℝ)^2+t+1))
  | .inr (.inr _) => 1/(2*(t:ℝ)^2+t+1)

theorem colourWeights_nonnegative (t : ℕ) : ∀ z, 0 ≤ colourWeights t z := by
  intro z
  rcases z with s | (⟨a,b,c⟩ | ⟨a,b⟩) <;> dsimp [colourWeights] <;> positivity

theorem indicator_weight (p : Prop) [Decidable p] (w : ℝ) :
    (if p then w else 0) = (if p then (1:ℝ) else 0)*w := by
  split <;> simp

theorem colour_coverage (t : ℕ)
    (v : Option (ZMod (2*t+1)) × Option (ZMod (2*t+1))) :
    (∑ z, if v ∈ (colourSets t z).val then colourWeights t z else 0) = 1 := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  dsimp only [colourSets,colourWeights]
  simp_rw [indicator_weight _ (1/(2*(t:ℝ)+1)),
    indicator_weight _ (1/(2*(2*(t:ℝ)+1)*(2*(t:ℝ)^2+t+1))),
    indicator_weight _ (1/(2*(t:ℝ)^2+t+1)),← Finset.sum_mul]
  rcases v with ⟨i,j⟩
  cases i with
  | none =>
    cases j with
    | none =>
      simp [family0,family1,family2,profileFamily,ZMod.card]
      field_simp
    | some j =>
      rw [family2_mixedB_count]
      simp [family0,family1,profileFamily,Fin.sum_univ_two,ZMod.card]
      have hd : (2*(t:ℝ)^2+t+1) ≠ 0 := by positivity
      have hm : (2*(t:ℝ)+1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  | some i =>
    cases j with
    | none =>
      rw [family2_mixedA_count]
      simp [family0,family1,profileFamily,Fin.sum_univ_two,ZMod.card]
      have hd : (2*(t:ℝ)^2+t+1) ≠ 0 := by positivity
      have hm : (2*(t:ℝ)+1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    | some j =>
      rw [family0_rim_count,family1_rim_count,family2_rim_count]
      have hd : (2*(t:ℝ)^2+t+1) ≠ 0 := by positivity
      have hm : (2*(t:ℝ)+1) ≠ 0 := by positivity
      field_simp
      ring

noncomputable def attainingColouring (t : ℕ) : FractionalColouring (wheelSquare t) :=
  indexedColouring (wheelSquare t) (colourSets t) (colourWeights t)
    (colourWeights_nonnegative t) (fun v => le_of_eq (colour_coverage t v).symm)

theorem attainingColouring_total (t : ℕ) :
    (attainingColouring t).total =
      (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+t+1) := by
  rw [attainingColouring,indexedColouring_total]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,colourWeights,ZMod.card]
  have hd : (2*(t:ℝ)^2+t+1) ≠ 0 := by positivity
  have hm : (2*(t:ℝ)+1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end WheelFormal
