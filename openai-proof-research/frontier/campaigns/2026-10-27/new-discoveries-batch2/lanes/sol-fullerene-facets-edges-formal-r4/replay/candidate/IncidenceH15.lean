import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH15 : ∀ v, active (AH 15) DH (PH v) ↔ v ∈ incidentH 15 := by decide +kernel
end TripleCertificates
