import R8Chain105561
namespace Percolation.MaskChain
set_option autoImplicit false
-- Precisely the semantic obligation for zero-based additions [106061,129671).
def RemainingSuffixUnsatR8 : Prop :=
  ¬ ∃ v : SatVar → Bool, (∀ c ∈ normalizedCNF5, CNF.Holds v c) ∧
    MaskRUP.Holds (v ∘ decodeVar) (5754986057962046098875290843988827640455757824, 2787593149816327892691964784081045188247552)
end Percolation.MaskChain
namespace Percolation
set_option autoImplicit false
theorem not_conjecture20_mask_after106061
    (h : MaskChain.RemainingSuffixUnsatR8) : ¬ Conjecture20 := by
  apply not_conjecture20_normalized
  rintro ⟨v,hv⟩
  exact h ⟨v,hv,MaskChain.clause155842 v hv⟩
#print axioms not_conjecture20_mask_after106061
#print not_conjecture20_mask_after106061
end Percolation
