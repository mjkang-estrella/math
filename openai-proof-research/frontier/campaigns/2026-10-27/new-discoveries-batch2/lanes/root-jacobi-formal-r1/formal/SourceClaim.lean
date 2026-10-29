import SourceUpperBound
import SourceSharpness

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JacobiShifted

/-- The closed literal source claim, with the pure-u coefficient witnessing sharpness. -/
theorem source_claim : SourceClaim := by
  intro r hr
  exact ⟨SourceBridge.sourceKappa_twoLocal r hr, SourceBridge.sourceKappa_pure_u_sharp r hr⟩

end JacobiShifted
