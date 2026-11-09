import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG19 : ∀ v, active (AG 19) DG (PG v) ↔ v ∈ incidentG 19 := by decide +kernel
end TripleCertificates
