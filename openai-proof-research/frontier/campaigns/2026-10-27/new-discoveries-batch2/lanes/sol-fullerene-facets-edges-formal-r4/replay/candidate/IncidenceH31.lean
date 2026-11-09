import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH31 : ∀ v, active (AH 31) DH (PH v) ↔ v ∈ incidentH 31 := by decide +kernel
end TripleCertificates
