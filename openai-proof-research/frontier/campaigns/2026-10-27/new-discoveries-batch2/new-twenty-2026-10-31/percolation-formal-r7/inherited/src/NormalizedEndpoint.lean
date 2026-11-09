import NReplay024
namespace Percolation.NReplay
-- Exactly the unreplayed normalized frontier refutation remains a hypothesis.
def NormalizedFrontierUnsat5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefix024, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after12500 (h : NormalizedFrontierUnsat5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,prefix_sound024 v hv⟩
#print axioms not_conjecture20_normalized_after12500
end Percolation.NReplay
