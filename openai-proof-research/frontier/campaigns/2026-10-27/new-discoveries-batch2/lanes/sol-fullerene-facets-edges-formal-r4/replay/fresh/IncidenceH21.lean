import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH21 : ∀ v, active (AH 21) DH (PH v) ↔ v ∈ incidentH 21 := by decide +kernel
end TripleCertificates
