import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG13 : ∀ v, active (AG 13) DG (PG v) ↔ v ∈ incidentG 13 := by decide +kernel
end TripleCertificates
