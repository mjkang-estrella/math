import NReplay259
namespace Percolation
 theorem generatedNormalizedUnsat5_closed : GeneratedNormalizedUnsat5 := by
  rintro ⟨v,hv⟩
  have h := NReplay.der_184281 v hv
  obtain ⟨z,hz,_⟩ := h
  cases hz
 theorem noMinimalTwoRound5_closed : NoMinimalTwoRound5 :=
  normalized_unsat_implies_noMinimal5 generatedNormalizedUnsat5_closed
 theorem not_conjecture20_unconditional : ¬ Conjecture20 :=
  not_conjecture20 noMinimalTwoRound5_closed
#print axioms generatedNormalizedUnsat5_closed
#print axioms noMinimalTwoRound5_closed
#print axioms not_conjecture20_unconditional
end Percolation
