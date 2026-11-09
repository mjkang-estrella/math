import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH06 : ∀ v, active (AH 6) DH (PH v) ↔ v ∈ incidentH 6 := by decide +kernel
end TripleCertificates
