import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG04 : ∀ v, active (AG 4) DG (PG v) ↔ v ∈ incidentG 4 := by decide +kernel
end TripleCertificates
