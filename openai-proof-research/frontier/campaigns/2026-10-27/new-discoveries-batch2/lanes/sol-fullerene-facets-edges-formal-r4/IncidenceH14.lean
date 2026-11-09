import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH14 : ∀ v, active (AH 14) DH (PH v) ↔ v ∈ incidentH 14 := by decide +kernel
end TripleCertificates
