import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG00 : ∀ v, active (AG 0) DG (PG v) ↔ v ∈ incidentG 0 := by decide +kernel
end TripleCertificates
