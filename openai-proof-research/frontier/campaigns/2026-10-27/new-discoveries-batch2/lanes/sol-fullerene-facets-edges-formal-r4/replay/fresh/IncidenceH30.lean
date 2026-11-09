import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH30 : ∀ v, active (AH 30) DH (PH v) ↔ v ∈ incidentH 30 := by decide +kernel
end TripleCertificates
