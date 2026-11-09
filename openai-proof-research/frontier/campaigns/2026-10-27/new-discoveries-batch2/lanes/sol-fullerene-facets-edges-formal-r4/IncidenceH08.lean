import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH08 : ∀ v, active (AH 8) DH (PH v) ↔ v ∈ incidentH 8 := by decide +kernel
end TripleCertificates
