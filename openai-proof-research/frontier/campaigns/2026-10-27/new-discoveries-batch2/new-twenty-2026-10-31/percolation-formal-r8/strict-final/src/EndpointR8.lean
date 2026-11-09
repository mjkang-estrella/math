import R8Chain129561
namespace Percolation
set_option autoImplicit false
abbrev NormalizedCNFUnsat5 := GeneratedNormalizedUnsat5
theorem normalizedCNFUnsat5 : NormalizedCNFUnsat5 := by
  rintro ⟨v, hv⟩
  obtain ⟨n, b, hn, _⟩ := MaskChain.clause184281 v hv
  cases b <;> simp [MaskRUP.bits, MaskChain.maskR8_184281] at hn
theorem noMinimalTwoRound5_unconditional : NoMinimalTwoRound5 :=
  normalized_unsat_implies_noMinimal5 normalizedCNFUnsat5
theorem not_conjecture20_unconditional : ¬ Conjecture20 :=
  not_conjecture20_normalized normalizedCNFUnsat5
#print axioms normalizedCNFUnsat5
#print axioms noMinimalTwoRound5_unconditional
#print axioms not_conjecture20_unconditional
#print not_conjecture20_unconditional
end Percolation
