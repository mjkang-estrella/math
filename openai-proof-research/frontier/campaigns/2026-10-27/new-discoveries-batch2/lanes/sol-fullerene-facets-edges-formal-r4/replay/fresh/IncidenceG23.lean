import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG23 : ∀ v, active (AG 23) DG (PG v) ↔ v ∈ incidentG 23 := by decide +kernel
end TripleCertificates
