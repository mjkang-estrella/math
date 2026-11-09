import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG08 : ∀ v, active (AG 8) DG (PG v) ↔ v ∈ incidentG 8 := by decide +kernel
end TripleCertificates
