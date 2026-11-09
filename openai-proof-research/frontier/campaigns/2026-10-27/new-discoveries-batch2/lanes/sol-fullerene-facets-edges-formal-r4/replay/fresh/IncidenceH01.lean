import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH01 : ∀ v, active (AH 1) DH (PH v) ↔ v ∈ incidentH 1 := by decide +kernel
end TripleCertificates
