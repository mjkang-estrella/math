import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG26 : ∀ v, active (AG 26) DG (PG v) ↔ v ∈ incidentG 26 := by decide +kernel
end TripleCertificates
