import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH02 : ∀ v, active (AH 2) DH (PH v) ↔ v ∈ incidentH 2 := by decide +kernel
end TripleCertificates
