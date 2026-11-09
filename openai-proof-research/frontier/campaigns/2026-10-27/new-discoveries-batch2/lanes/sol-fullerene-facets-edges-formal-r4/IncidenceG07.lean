import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG07 : ∀ v, active (AG 7) DG (PG v) ↔ v ∈ incidentG 7 := by decide +kernel
end TripleCertificates
