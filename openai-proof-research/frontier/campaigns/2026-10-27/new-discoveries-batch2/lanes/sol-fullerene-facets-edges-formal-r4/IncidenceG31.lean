import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem incidenceG31 : ∀ v, active (AG 31) DG (PG v) ↔ v ∈ incidentG 31 := by decide +kernel
end TripleCertificates
