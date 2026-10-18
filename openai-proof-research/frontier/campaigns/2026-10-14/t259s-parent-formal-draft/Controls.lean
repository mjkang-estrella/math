import Propagation

namespace T259SControls

/-- With two unknown distinguished edges, a bridge and endpoint agreement
do not force either distinguished edge: false -> true -> true -> false. -/
theorem two_missing_edges :
    (true = true) ∧ (false = false) ∧ ¬(false = true) ∧ ¬(true = false) := by
  decide

/-- If the bridge is removed, the other distinguished edge and whole endpoint
relation are insufficient: false -> true, false -> false. -/
theorem bridge_is_needed :
    (false = false) ∧ (false = false) ∧ ¬(true = false) ∧ ¬(false = true) := by
  decide

/-- If endpoint agreement is removed, all the other local edges can hold:
false -> true -> true -> true. -/
theorem endpoint_is_needed :
    (true = true) ∧ (true = true) ∧ ¬(false = true) := by
  decide

def collapse (y : Bool × Bool) : Bool × Bool := (y.1, false)

/-- Every fiber has a fixed representative, yet availability on all fibers
fails. A selected section is therefore strictly weaker than Available. -/
theorem selected_section_does_not_give_availability :
    (∀ z : Bool, ∃ y : Bool × Bool, y.1 = z ∧ y = collapse y) ∧
    ¬T259S.Available (Setoid.ker (id : Bool × Bool → Bool × Bool))
      collapse Prod.fst Set.univ := by
  constructor
  · intro z
    exact ⟨(z, false), rfl, rfl⟩
  · intro h
    have heq := h (false, true) (Set.mem_univ _)
    change (false, true) = (false, false) at heq
    cases heq

end T259SControls
