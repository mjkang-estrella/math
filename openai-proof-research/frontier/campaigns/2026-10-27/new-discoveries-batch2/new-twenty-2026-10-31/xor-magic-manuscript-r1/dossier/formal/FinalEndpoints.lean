import FinalExistence
import UniformObstruction
namespace XorMagic
/-- The printed endpoint is forbidden uniformly, independently of the construction. -/
theorem not_printed_each_ge_four : ∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n :=
  XorMagicFinal.not_printed_ge_four_uniform

/-- Re-export of the inherited negation with no lower bound on n. -/
theorem printed_not_all : ¬ (∀ n : ℕ, PrintedAt n) := not_printed_all
/-- Re-export of the inherited positive-n negation. -/
theorem printed_not_positive : ¬ (∀ n : ℕ, 0 < n → PrintedAt n) := not_printed_positive
end XorMagic
#print axioms XorMagic.corrected_all
#print axioms XorMagic.not_printed_each_ge_four
#print axioms XorMagic.printed_not_all
#print axioms XorMagic.printed_not_positive
