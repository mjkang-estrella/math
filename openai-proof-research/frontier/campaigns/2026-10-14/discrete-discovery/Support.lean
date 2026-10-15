import Mathlib

/- Supporting finite identities only. No Liouville or process theorem is asserted. -/
namespace DiscreteDiscovery

def sgn (b : Bool) : ℤ := if b then 1 else -1

def y (x : Fin 7 → Bool) (j : Fin 3) : ℤ :=
  sgn (x ⟨j.val, by omega⟩) * sgn (x ⟨j.val + 1, by omega⟩) *
  sgn (x ⟨j.val + 3, by omega⟩) * sgn (x ⟨j.val + 4, by omega⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem three_shift_telescope :
    ∀ x : Fin 7 → Bool, y x 0 * y x 1 * y x 2 = sgn (x 0) * sgn (x 6) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem three_shift_signed_bound :
    ∀ (x : Fin 7 → Bool) (s : Bool),
      sgn s * (y x 0 + y x 1 + y x 2) ≤ 2 + sgn s * sgn (x 0) * sgn (x 6) := by
  decide

#print axioms three_shift_telescope
#print axioms three_shift_signed_bound
end DiscreteDiscovery
