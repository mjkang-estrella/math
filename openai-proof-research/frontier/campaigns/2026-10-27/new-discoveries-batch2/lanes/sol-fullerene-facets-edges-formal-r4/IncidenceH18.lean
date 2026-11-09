import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH18 : ∀ v, active (AH 18) DH (PH v) ↔ v ∈ incidentH 18 := by decide +kernel
end TripleCertificates
