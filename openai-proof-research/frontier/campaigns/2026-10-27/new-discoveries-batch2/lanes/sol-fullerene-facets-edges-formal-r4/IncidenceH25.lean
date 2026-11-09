import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH25 : ∀ v, active (AH 25) DH (PH v) ↔ v ∈ incidentH 25 := by decide +kernel
end TripleCertificates
