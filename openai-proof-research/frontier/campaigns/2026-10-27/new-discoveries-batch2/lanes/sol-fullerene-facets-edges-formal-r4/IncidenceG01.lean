import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG01 : ∀ v, active (AG 1) DG (PG v) ↔ v ∈ incidentG 1 := by decide +kernel
end TripleCertificates
