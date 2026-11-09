import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG09 : ∀ v, active (AG 9) DG (PG v) ↔ v ∈ incidentG 9 := by decide +kernel
end TripleCertificates
