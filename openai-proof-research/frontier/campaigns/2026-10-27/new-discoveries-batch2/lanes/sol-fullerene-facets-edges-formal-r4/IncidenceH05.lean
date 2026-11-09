import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH05 : ∀ v, active (AH 5) DH (PH v) ↔ v ∈ incidentH 5 := by decide +kernel
end TripleCertificates
