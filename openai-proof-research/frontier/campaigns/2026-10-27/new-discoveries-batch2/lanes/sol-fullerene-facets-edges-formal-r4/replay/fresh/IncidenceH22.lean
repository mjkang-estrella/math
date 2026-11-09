import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH22 : ∀ v, active (AH 22) DH (PH v) ↔ v ∈ incidentH 22 := by decide +kernel
end TripleCertificates
