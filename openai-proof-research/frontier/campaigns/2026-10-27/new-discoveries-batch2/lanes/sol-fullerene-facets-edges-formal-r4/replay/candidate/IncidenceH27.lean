import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH27 : ∀ v, active (AH 27) DH (PH v) ↔ v ∈ incidentH 27 := by decide +kernel
end TripleCertificates
