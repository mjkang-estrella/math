import TR135168
import TR135200
import TR135232
import TR135264
set_option autoImplicit false
namespace Polyomino57
theorem F11B066Placed (row : List GridPoint) (h : FamilyMember row F11B066) : ∃ t, translate t row.toFinset ⊆ witness := by
  exact h.elim (fun h => h.elim (fun h => TR135168_placed row h) (fun h => TR135200_placed row h)) (fun h => h.elim (fun h => TR135232_placed row h) (fun h => TR135264_placed row h))
end Polyomino57
