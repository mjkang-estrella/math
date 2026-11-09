import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH10 : ∀ v, active (AH 10) DH (PH v) ↔ v ∈ incidentH 10 := by decide +kernel
end TripleCertificates
