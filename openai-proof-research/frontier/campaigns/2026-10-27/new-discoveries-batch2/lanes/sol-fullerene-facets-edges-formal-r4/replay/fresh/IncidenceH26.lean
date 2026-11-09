import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH26 : ∀ v, active (AH 26) DH (PH v) ↔ v ∈ incidentH 26 := by decide +kernel
end TripleCertificates
