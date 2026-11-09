import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG11 : ∀ v, active (AG 11) DG (PG v) ↔ v ∈ incidentG 11 := by decide +kernel
end TripleCertificates
