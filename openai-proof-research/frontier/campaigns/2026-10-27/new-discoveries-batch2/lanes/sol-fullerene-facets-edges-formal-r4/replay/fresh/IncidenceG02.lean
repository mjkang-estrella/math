import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG02 : ∀ v, active (AG 2) DG (PG v) ↔ v ∈ incidentG 2 := by decide +kernel
end TripleCertificates
