import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG16 : ∀ v, active (AG 16) DG (PG v) ↔ v ∈ incidentG 16 := by decide +kernel
end TripleCertificates
