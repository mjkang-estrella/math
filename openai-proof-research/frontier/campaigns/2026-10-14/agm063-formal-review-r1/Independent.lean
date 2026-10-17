import AGM063
open AGM063
namespace Independent

def budgetDegree (a : Bool) : ℤ := if a then 3 else 2

theorem sharp_degree_budget :
    (∀ a, (2 : ℤ) ≤ budgetDegree a) ∧
    (∑ a : Bool, (budgetDegree a - 1)) = (Fintype.card Bool : ℤ) * (2 - 1) + 1 ∧
    (∀ a, budgetDegree a < 2 * 2) := by
  norm_num [budgetDegree, Fintype.sum_bool]

def badDegree (a : Bool) : ℤ := if a then 4 else 1

theorem minimum_degree_essential :
    (∑ a : Bool, (badDegree a - 1)) ≤ (Fintype.card Bool : ℤ) * (2 - 1) + 1 ∧
    ¬ (badDegree true < 2 * 2) := by norm_num [badDegree, Fintype.sum_bool]

def inward (x y : Bool) : Prop := x = true ∧ y = false

theorem one_way_saturation_insufficient :
    Preserves inward ({false} : Set Bool) ∧
    ¬ Saturated inward ({false} : Set Bool) := by
  constructor
  · intro x y h hx
    simp only [inward] at h
    simp [h.2]
  · intro h
    have h' := h (x := true) (y := false) (by simp [inward])
    simp at h'

theorem quotient_constancy_essential :
    Saturated (fun _ _ : Bool => True) Set.univ ∧
    (false,true) ∉ fiberPairs (Set.univ : Set Bool) (fun x => x.val) := by
  constructor
  · intro x y h
    simp
  · simp [fiberPairs]

theorem nonempty_nonspanning :
    ({(0 : ℝ)} : Finset ℝ).Nonempty ∧
    (∀ v ∈ ({(0 : ℝ)} : Finset ℝ), (LinearMap.id : ℝ →ₗ[ℝ] ℝ) v = 0) ∧
    (0 : ℝ) < (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 := by simp

theorem integer_multiplicity_essential :
    (0 : ℚ) < 2 ∧ 2 ≤ (2 : ℚ) ∧ 1 ≤ (3/2 : ℚ) ∧
    (3/2 : ℚ) * 2 < 2 * 2 ∧ (3/2 : ℚ) ≠ 1 := by norm_num

theorem integer_pseudoindex_essential :
    (3 : ℚ) ≥ 3 ∧ (2 : ℚ) ≤ 5/2 ∧
    ((3 : ℚ) - 1) * (5/2 - 2) ≤ 1 ∧ (5/2 : ℚ) ≠ 2 := by norm_num

theorem sharp_dimension :
    (2 * (4 : ℤ) - 1 ≤ 7) ∧ (7 ≤ max (2 * 4 - 1) (2 * 4 - 2)) ∧
    ¬ (7 ≤ max (2 * (4 : ℤ) - 2) (2 * 4 - 2)) := by norm_num

theorem properness_and_nonempty_essential :
    Preserves (fun _ _ : Bool => True) Set.univ ∧
    Preserves (fun _ _ : Bool => True) ∅ ∧
    (∀ x y : Bool, Relation.ReflTransGen (fun _ _ => True) x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h hx; trivial
  · intro x y h hx; exact False.elim hx
  · intro x y; exact Relation.ReflTransGen.single trivial
end Independent
