import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG27 : ∀ v, active (AG 27) DG (PG v) ↔ v ∈ incidentG 27 := by decide +kernel
end TripleCertificates
