import IncidenceDataH
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace TripleCertificates
theorem positiveH : ∀ v, 0 < (PH v).den := by decide +kernel
theorem injectiveH : ∀ v w, same (PH v) (PH w) → v = w := by decide +kernel
theorem incident_cardH : ∀ i, (incidentH i).card = if i ∈ pentagonIdsH then 5 else 6 := by decide +kernel
theorem incident_separateH : ∀ i j, i ≠ j → ∃ v ∈ incidentH i, v ∉ incidentH j := by decide +kernel
theorem five_countH : pentagonIdsH.card = 12 := by decide +kernel
theorem six_countH : (Finset.univ \ pentagonIdsH).card = 20 := by decide +kernel
end TripleCertificates
