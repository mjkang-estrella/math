import TabMinors
/-! Positive fidelity controls against the source (arXiv:2307.13161). -/
namespace TabMinors.Controls
open TabMinors
/-- Source Figure "cell deletion via jeu de taquin": `T - 8`. -/
def Tfig : Tab := [[1,2,3,4,5],[6,7,8,9,18],[10,11,12,17],[13,16],[14],[15]]
def Tfig8 : Tab := [[1,2,3,4,5],[6,7,8,16,17],[9,10,11],[12,15],[13],[14]]
theorem fig_syt : IsSYT 18 Tfig := by decide +kernel
theorem fig_del : del Tfig 8 = Tfig8 := by decide +kernel
/-- Source Figure "same 2-minors" (n = 7): equal *sets* of 2-minors. -/
def S₁ : Tab := [[1,2,5,7],[3,4,6]]
def S₂ : Tab := [[1,3,5,7],[2,4,6]]
theorem same_sets : (∀ x ∈ minors 2 S₁, x ∈ minors 2 S₂) ∧ (∀ x ∈ minors 2 S₂, x ∈ minors 2 S₁) := by
  decide +kernel
/-- …but the multisets differ (the source states `mM_2` is injective at `n = 7`). -/
theorem diff_multisets : minors 2 S₁ ≠ minors 2 S₂ := by decide +kernel
end TabMinors.Controls
