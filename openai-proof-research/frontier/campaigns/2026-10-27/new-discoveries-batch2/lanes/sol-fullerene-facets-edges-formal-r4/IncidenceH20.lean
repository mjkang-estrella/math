import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH20 : ∀ v, active (AH 20) DH (PH v) ↔ v ∈ incidentH 20 := by decide +kernel
end TripleCertificates
