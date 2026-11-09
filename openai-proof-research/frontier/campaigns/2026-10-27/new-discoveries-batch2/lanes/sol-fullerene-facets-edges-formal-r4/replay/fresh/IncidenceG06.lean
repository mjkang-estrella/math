import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG06 : ∀ v, active (AG 6) DG (PG v) ↔ v ∈ incidentG 6 := by decide +kernel
end TripleCertificates
