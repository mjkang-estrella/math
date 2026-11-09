import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH07 : ∀ v, active (AH 7) DH (PH v) ↔ v ∈ incidentH 7 := by decide +kernel
end TripleCertificates
