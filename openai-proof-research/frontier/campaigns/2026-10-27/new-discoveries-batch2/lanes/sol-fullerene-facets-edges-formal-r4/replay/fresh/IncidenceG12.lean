import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG12 : ∀ v, active (AG 12) DG (PG v) ↔ v ∈ incidentG 12 := by decide +kernel
end TripleCertificates
