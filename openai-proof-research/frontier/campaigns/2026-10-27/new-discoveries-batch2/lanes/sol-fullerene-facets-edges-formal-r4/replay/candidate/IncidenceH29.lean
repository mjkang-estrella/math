import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH29 : ∀ v, active (AH 29) DH (PH v) ↔ v ∈ incidentH 29 := by decide +kernel
end TripleCertificates
