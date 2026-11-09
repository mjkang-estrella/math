import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH16 : ∀ v, active (AH 16) DH (PH v) ↔ v ∈ incidentH 16 := by decide +kernel
end TripleCertificates
