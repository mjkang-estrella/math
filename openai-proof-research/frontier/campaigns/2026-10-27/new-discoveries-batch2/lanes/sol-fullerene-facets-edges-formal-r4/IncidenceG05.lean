import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG05 : ∀ v, active (AG 5) DG (PG v) ↔ v ∈ incidentG 5 := by decide +kernel
end TripleCertificates
