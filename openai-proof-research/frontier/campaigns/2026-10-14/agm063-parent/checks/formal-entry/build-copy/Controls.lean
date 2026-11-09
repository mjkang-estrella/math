/- Copyright 2026 Myeongjin Kang. MIT. Concrete semantic boundary controls. -/
import AGM063
namespace AGMControls
open AGM063

def leftPoint : Set Bool := {false}
def universalPair : Bool → Bool → Prop := fun _ _ => True

theorem unsaturated_mixed_pair :
    (false,true) ∈ relationPairs universalPair ∧
    (false,true) ∉ ((relationPairs universalPair ∩ (leftPoint ×ˢ leftPoint)) ∪
      (leftPointᶜ ×ˢ leftPointᶜ)) := by
  simp [relationPairs, universalPair, leftPoint]

theorem weak_dimension_premises :
    2 * (3 : ℤ) - 1 ≤ 5 ∧ 5 ≤ max (2 * 3 - 2) (2 * 3 - 1) := by norm_num

theorem weak_dimension_conclusion_false : ¬ ((2 : ℤ) ≤ 1) := by norm_num

theorem pseudoindex_one_budget :
    ∑ _a : Fin 1, ((2 : ℤ) - 1) ≤ (Fintype.card (Fin 1) : ℤ) * (1 - 1) + 1 := by
  norm_num

theorem pseudoindex_one_cutoff_false : ¬ ((2 : ℤ) < 2 * 1) := by norm_num

theorem cutoff_equality_allows_two :
    (∀ _a : Fin 2, (2 : ℤ) ≤ 2) ∧
    (∑ _a : Fin 2, (2 : ℤ)) = 2 * 2 ∧ Fintype.card (Fin 2) = 2 := by
  norm_num

theorem empty_set_vanishing :
    ∀ v ∈ (∅ : Finset ℝ), (LinearMap.id : ℝ →ₗ[ℝ] ℝ) v = 0 := by simp

theorem functional_not_zero : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 ≠ 0 := by norm_num

def step : Bool → Bool → Prop := fun x y => x = false ∧ y = true

theorem actual_chain_escapes :
    Relation.ReflTransGen step false true ∧ false ∈ leftPoint ∧ true ∉ leftPoint := by
  refine ⟨Relation.ReflTransGen.tail Relation.ReflTransGen.refl ⟨rfl,rfl⟩, ?_, ?_⟩ <;>
    simp [leftPoint]

theorem reversed_pseudoindex_premises :
    (2 : ℤ) ≤ 2 ∧ 2 ≤ 3 ∧ 5 - 1 ≤ 2 * (3 - 1) := by norm_num

theorem reversed_pseudoindex_conclusion_false :
    ¬ (((5 : ℤ) - 3 + 1) - 1 ≤ (2 - 1) * (2 - 1)) := by norm_num
end AGMControls
