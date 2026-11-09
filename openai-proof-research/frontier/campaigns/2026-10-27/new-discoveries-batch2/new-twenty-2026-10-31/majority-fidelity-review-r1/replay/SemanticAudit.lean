import Majority
noncomputable section
#print Majority.mathdb_326640
#check @Majority.arc_orientation
#check @Majority.orientation_representation
#check @Majority.gamma_minimum
#check @Majority.DOM_maximum
#check @Majority.majority_criterion
#check @Majority.ceiling_spelling
#print axioms Majority.pair_card
#print axioms Majority.pair_strict
#print axioms Majority.extend

local instance (p : Prop) : Decidable p := Classical.propDecidable p
example (r s : ℕ) (E : Fin r → Fin s → Bool) (X : Set (Fin r ⊕ Fin s))
    (v : Fin r ⊕ Fin s) :
    v ∈ Majority.cover E X.toFinset ↔ v ∈ X ∨ ∃ u ∈ X, Majority.arc E u v := by
  classical
  simp only [Majority.mem_cover, Set.mem_toFinset]
