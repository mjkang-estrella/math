import Controls
import Semantics
namespace Endpoint
open Literal Concrete
/-- Two residual obligations, stated on the literal matrix definitions. -/
def PureLowerBound : Prop := ∀ k, Pure g0 k → 11 ≤ k.order
def ChainAbsence : Prop := ¬ HasChain g7

theorem conditional_negation (lower : PureLowerBound) (noChain : ChainAbsence) :
    ¬ Conjecture51 := by
  apply refutation_from_counterexample original_doubled_cubic pure_path
    (fun k hk => lower k hk) noChain seven_move_witness order_drop
#print axioms conditional_negation
end Endpoint
