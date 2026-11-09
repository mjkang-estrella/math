import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH12 : ∀ v, active (AH 12) DH (PH v) ↔ v ∈ incidentH 12 := by decide +kernel
end TripleCertificates
