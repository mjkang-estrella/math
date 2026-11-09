import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG21 : ∀ v, active (AG 21) DG (PG v) ↔ v ∈ incidentG 21 := by decide +kernel
end TripleCertificates
