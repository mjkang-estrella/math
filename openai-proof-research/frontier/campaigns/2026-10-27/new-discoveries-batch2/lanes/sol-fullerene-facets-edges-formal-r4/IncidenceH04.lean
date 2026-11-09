import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceH04 : ∀ v, active (AH 4) DH (PH v) ↔ v ∈ incidentH 4 := by decide +kernel
end TripleCertificates
