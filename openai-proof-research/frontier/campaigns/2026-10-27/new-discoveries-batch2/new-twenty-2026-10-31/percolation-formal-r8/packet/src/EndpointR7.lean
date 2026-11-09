import MaskChain0049
namespace Percolation.MaskChain
set_option autoImplicit false
-- The unreplayed suffix is precisely zero-based additions [5000,129671).
-- This semantic obligation suffices to close the last proved frontier clause.
def RemainingSuffixUnsatR7 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    MaskRUP.Holds (v ∘ decodeVar) (2495223039294576003288924160, 1208935042986666046259200)
end Percolation.MaskChain
namespace Percolation
set_option autoImplicit false
theorem not_conjecture20_mask_after5000
    (h : MaskChain.RemainingSuffixUnsatR7) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,MaskChain.clause27303 v hv⟩
#print axioms not_conjecture20_mask_after5000
#print axioms MaskChain.clause27303
#print not_conjecture20_mask_after5000
end Percolation
