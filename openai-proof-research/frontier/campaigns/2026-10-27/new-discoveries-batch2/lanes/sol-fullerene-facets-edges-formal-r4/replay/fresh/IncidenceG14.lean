import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG14 : ∀ v, active (AG 14) DG (PG v) ↔ v ∈ incidentG 14 := by decide +kernel
end TripleCertificates
