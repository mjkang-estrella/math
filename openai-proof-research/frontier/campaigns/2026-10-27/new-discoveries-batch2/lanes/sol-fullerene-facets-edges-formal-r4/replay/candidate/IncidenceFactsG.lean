import IncidenceDataG
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem positiveG : ∀ v, 0 < (PG v).den := by decide +kernel
theorem injectiveG : ∀ v w, same (PG v) (PG w) → v = w := by decide +kernel
theorem incident_cardG : ∀ i, (incidentG i).card = if i ∈ pentagonIdsG then 5 else 6 := by decide +kernel
theorem incident_separateG : ∀ i j, i ≠ j → ∃ v ∈ incidentG i, v ∉ incidentG j := by decide +kernel
theorem five_countG : pentagonIdsG.card = 12 := by decide +kernel
theorem six_countG : (Finset.univ \ pentagonIdsG).card = 20 := by decide +kernel
end TripleCertificates
