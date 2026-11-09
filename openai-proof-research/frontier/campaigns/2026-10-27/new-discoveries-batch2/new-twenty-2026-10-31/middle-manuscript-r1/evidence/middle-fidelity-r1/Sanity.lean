import MiddleFinal
namespace IndependentReview
open R139.MiddleOCD
instance : DecidableRel (middle G8).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [middle] <;> infer_instance
example : Fintype.card (Fin 8 ⊕ G8.edgeSet) = 19 := by decide
example : G8.edgeFinset.card = 11 := by decide
example : (middle G8).edgeFinset.card = 48 := by decide
example : ¬ IsDominating G8 ({0} : Finset (Fin 8)) := by
  intro h
  exact (by decide : ¬ (2 ∈ ({0} : Finset (Fin 8)) ∨ ∃ w ∈ ({0} : Finset (Fin 8)), G8.Adj 2 w)) (h 2)
example : IsDominating G8 ({6,7} : Finset (Fin 8)) := by unfold IsDominating; decide
example : ¬ IsOuterConnected G8 ({6,7} : Finset (Fin 8)) := by
  exact not_preconnected_of_closed G8 _ (↑({0,1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide)
example : ¬ IsOuterConnected' G8 ({6,7} : Finset (Fin 8)) := by
  intro h
  exact not_preconnected_of_closed G8 _ (↑({0,1} : Finset (Fin 8)))
    (by decide) 0 2 (by decide) (by decide) (by decide) (by decide) h.preconnected
example : ¬ (middle G8).Adj (Sum.inl 0) (Sum.inl 1) := by decide
example : IsOCD' G8 S0 := ⟨S0_dom, S0_conn⟩
example : IsOCD' (middle G8) D8 := ⟨D8_dom, M8_conn⟩
example : ocd G8 = 4 ∧ ocd' G8 = 4 ∧ ocd (middle G8) = 4 ∧ ocd' (middle G8) = 4 :=
  ⟨ocd_G8, ocd'_G8, ocd_M8, ocd'_M8⟩
example : IsOuterConnected G8 Finset.univ := by
  intro a
  exact False.elim (a.property (Finset.mem_univ a.val))
example : ¬ IsOuterConnected' G8 Finset.univ := by
  intro h
  obtain ⟨a⟩ := h.nonempty
  exact a.property (Finset.mem_univ a.val)
end IndependentReview
#print axioms R139.MiddleOCD.g8_value
#print axioms R139.MiddleOCD.g8_value'
#print axioms R139.MiddleOCD.middle_g8_value
#print axioms R139.MiddleOCD.middle_g8_value'
#print axioms R139.MiddleOCD.mathdb_355217_connected
#print axioms R139.MiddleOCD.mathdb_355217_connected'
#print axioms R139.MiddleOCD.edgeless_two_literal_failure
#print axioms R139.MiddleOCD.G8_connected
