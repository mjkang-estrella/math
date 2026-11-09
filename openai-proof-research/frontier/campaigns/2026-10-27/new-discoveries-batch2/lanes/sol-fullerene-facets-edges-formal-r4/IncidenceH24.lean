import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH24 : ∀ v, active (AH 24) DH (PH v) ↔ v ∈ incidentH 24 := by decide +kernel
end TripleCertificates
