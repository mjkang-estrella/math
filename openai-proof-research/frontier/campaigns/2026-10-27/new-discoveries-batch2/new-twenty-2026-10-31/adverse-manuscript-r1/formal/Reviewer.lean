import Main
import Lean.Util.CollectAxioms
namespace IndependentReview
open Adverse381433
-- Non-completeness stated without depending on a library convention.
def NonComplete {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ a b : V, a ≠ b ∧ ¬G.Adj a b
noncomputable def SourceRestatement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (∃ a b, G.Adj a b) → NonComplete G →
    (∀ v, ∃ w, G.Adj v w) →
    (∃ k : ℤ, upsilon G = k) →
    (∃ k : ℤ, leastEigenvalue G = k) →
    (∀ v, upsilon (deleteOpen G v) = upsilon G ∧
      leastEigenvalue (deleteOpen G v) = leastEigenvalue G) →
    (alpha G : ℝ) = upsilon G
 theorem noncomplete : NonComplete latinGraph := by
  refine ⟨(0,0),(1,1), by decide, ?_⟩
  change ¬((0,0) ≠ (1,1) ∧ _)
  decide
 theorem refutes_stricter_source : ¬SourceRestatement := by
  intro h
  have ha := graph_adverse
  exact graph_not_Q (h Cell latinGraph
    ⟨(0,0),(0,1), by unfold latinGraph; decide⟩ noncomplete
    ha.1 ha.2.1 ha.2.2.1 ha.2.2.2)
end IndependentReview
#print axioms IndependentReview.refutes_stricter_source
