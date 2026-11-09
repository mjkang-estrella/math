import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH23 : ∀ v, active (AH 23) DH (PH v) ↔ v ∈ incidentH 23 := by decide +kernel
end TripleCertificates
