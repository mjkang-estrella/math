import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG22 : ∀ v, active (AG 22) DG (PG v) ↔ v ∈ incidentG 22 := by decide +kernel
end TripleCertificates
