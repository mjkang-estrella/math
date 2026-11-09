import Endpoint
import RawResult
namespace Final
open Literal Concrete
/-- Residual transport of an arbitrarily relabelled literal reduction sequence
    to the canonically numbered list-matrix operation certified by the DAG. -/
def CanonicalTransport : Prop := ∀ k, Literal.Pure g0 k →
  ∃ rows, RawClosure.Pure Delta153.original rows ∧ rows.length = k.order

theorem conditional_literal_negation (transport : CanonicalTransport)
    (noChain : Endpoint.ChainAbsence) : ¬ Literal.Conjecture51 := by
  apply Endpoint.conditional_negation
  · intro k path
    obtain ⟨rows, hr, size⟩ := transport k path
    rw [← size]
    exact RawCert.canonical_original_lower rows hr
  · exact noChain
#print axioms conditional_literal_negation
end Final
