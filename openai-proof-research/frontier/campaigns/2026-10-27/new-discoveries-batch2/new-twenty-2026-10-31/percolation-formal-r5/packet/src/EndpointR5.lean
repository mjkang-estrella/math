import ReplayR5_0004
namespace Percolation.NReplay
def RemainingSuffixUnsatR5 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    (∀ c ∈ prefixR5_0004, CNF.Holds (v ∘ decodeVar) c)
theorem not_conjecture20_normalized_after13561 (h : RemainingSuffixUnsatR5) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,prefix_soundR5_0004 v hv⟩
#print axioms not_conjecture20_normalized_after13561
end Percolation.NReplay
