import Endpoint
import CanonicalStep
import ChainAbsence
namespace Round2
/-- The only certificate proposition still needed for the literal endpoint. -/
def CanonicalLowerBound : Prop := ∀ rows, RawClosure.Pure Delta153.original rows → 11 ≤ rows.length
 theorem literal_lower_bound (bound : CanonicalLowerBound) : Endpoint.PureLowerBound := by
  intro k path
  obtain ⟨rows,hp,ho⟩ := Transport.canonical_transport path
  rw [← ho]
  exact bound rows hp
 theorem conditional_negation (bound : CanonicalLowerBound) : ¬ Literal.Conjecture51 :=
  Endpoint.conditional_negation (literal_lower_bound bound) ChainPrefix.no_chain
#print axioms literal_lower_bound
#print axioms conditional_negation
end Round2
