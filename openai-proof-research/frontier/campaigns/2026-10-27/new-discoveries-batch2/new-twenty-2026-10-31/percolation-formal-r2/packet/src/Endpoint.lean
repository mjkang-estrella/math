import Structure
import Control4
import Control5
namespace Percolation
-- The single remaining mathematical obligation; this is a definition, not an assertion.
def NoMinimalTwoRound5 : Prop := ¬ ∃ a : Infection 5, Minimal PG5 5 a ∧ TimeIs PG5 5 a 2

theorem not_conjecture20 (remaining : NoMinimalTwoRound5) : ¬ Conjecture20 := by
  intro h
  exact remaining (h 5 PG5 5 (by decide) (by decide))

#print axioms not_conjecture20
#print axioms control4
#print axioms control5
#print axioms incidence_dot
#print axioms PG5
end Percolation
