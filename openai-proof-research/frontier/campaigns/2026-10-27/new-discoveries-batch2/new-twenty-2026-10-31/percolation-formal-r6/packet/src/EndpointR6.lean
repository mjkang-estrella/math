import Normalize
import MaskCNF
namespace Percolation
set_option autoImplicit false
abbrev NormalizedCNFUnsat5 : Prop := GeneratedNormalizedUnsat5
-- All certificate additions remain to be connected to the generator in round 6.
theorem not_conjecture20_mask_conditional (h : NormalizedCNFUnsat5) : ¬ Conjecture20 :=
  not_conjecture20_normalized h
#print axioms not_conjecture20_mask_conditional
end Percolation
