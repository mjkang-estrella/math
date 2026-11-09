import ReplayR5_0023
namespace Percolation.NReplay
def RemainingSuffixUnsatR5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefixR5_0023, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after17500 (h : RemainingSuffixUnsatR5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,prefix_soundR5_0023 v hv⟩
#print axioms not_conjecture20_normalized_after17500
end Percolation.NReplay
