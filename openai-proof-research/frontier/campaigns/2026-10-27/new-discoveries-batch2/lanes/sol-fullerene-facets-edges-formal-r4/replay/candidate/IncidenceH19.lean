import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH19 : ∀ v, active (AH 19) DH (PH v) ↔ v ∈ incidentH 19 := by decide +kernel
end TripleCertificates
