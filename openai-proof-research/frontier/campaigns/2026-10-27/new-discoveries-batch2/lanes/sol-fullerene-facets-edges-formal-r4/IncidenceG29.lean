import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG29 : ∀ v, active (AG 29) DG (PG v) ↔ v ∈ incidentG 29 := by decide +kernel
end TripleCertificates
