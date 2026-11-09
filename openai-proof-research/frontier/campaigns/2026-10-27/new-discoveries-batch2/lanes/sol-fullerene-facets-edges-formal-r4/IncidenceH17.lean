import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH17 : ∀ v, active (AH 17) DH (PH v) ↔ v ∈ incidentH 17 := by decide +kernel
end TripleCertificates
