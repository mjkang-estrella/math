import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG10 : ∀ v, active (AG 10) DG (PG v) ↔ v ∈ incidentG 10 := by decide +kernel
end TripleCertificates
