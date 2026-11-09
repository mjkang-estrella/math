import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH09 : ∀ v, active (AH 9) DH (PH v) ↔ v ∈ incidentH 9 := by decide +kernel
end TripleCertificates
