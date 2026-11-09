import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH03 : ∀ v, active (AH 3) DH (PH v) ↔ v ∈ incidentH 3 := by decide +kernel
end TripleCertificates
