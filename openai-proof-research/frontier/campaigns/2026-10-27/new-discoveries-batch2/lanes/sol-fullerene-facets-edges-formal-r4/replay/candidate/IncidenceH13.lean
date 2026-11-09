import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH13 : ∀ v, active (AH 13) DH (PH v) ↔ v ∈ incidentH 13 := by decide +kernel
end TripleCertificates
