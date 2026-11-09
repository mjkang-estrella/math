import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG15 : ∀ v, active (AG 15) DG (PG v) ↔ v ∈ incidentG 15 := by decide +kernel
end TripleCertificates
