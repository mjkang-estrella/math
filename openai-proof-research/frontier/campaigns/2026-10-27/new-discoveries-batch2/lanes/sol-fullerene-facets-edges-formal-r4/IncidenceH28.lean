import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH28 : ∀ v, active (AH 28) DH (PH v) ↔ v ∈ incidentH 28 := by decide +kernel
end TripleCertificates
