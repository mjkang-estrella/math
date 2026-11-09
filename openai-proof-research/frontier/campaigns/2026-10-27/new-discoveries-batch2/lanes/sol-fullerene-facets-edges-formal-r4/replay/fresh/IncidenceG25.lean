import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG25 : ∀ v, active (AG 25) DG (PG v) ↔ v ∈ incidentG 25 := by decide +kernel
end TripleCertificates
