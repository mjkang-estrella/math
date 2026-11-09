import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH11 : ∀ v, active (AH 11) DH (PH v) ↔ v ∈ incidentH 11 := by decide +kernel
end TripleCertificates
