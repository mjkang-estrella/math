import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG24 : ∀ v, active (AG 24) DG (PG v) ↔ v ∈ incidentG 24 := by decide +kernel
end TripleCertificates
