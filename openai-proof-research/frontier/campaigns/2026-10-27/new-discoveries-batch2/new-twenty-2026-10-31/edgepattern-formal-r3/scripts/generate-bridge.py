from pathlib import Path
from itertools import product
names=[''.join(map(str,k)) for k in product(range(3),repeat=4)]
s=''.join(f'import EvalR3_{k}\n' for k in names)+'''import InvarianceR2
import ReductionR2
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem all_81 (k : Counts) :
    1 ≤ ∑ i : Fin 3, Concrete.alpha i * expectation (pattern k) i := by
  simp_rw [expectation_eq]
  obtain ⟨a,b,c,d⟩ := k
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
'''
s+='\n'.join('  · exact bound_'+k for k in names)+'\n'
s+='''
universe u

theorem bound_of_iso {W : Type u} [Fintype W] (T : Rooted W) (k : Counts)
    (e : RootedIso T (pattern k)) :
    1 ≤ ∑ i : Fin 3, Concrete.alpha i * expectation T i := by
  have h := all_81 k
  simpa only [e.expectation_eq] using h

-- This missing universal classification is explicit, never an axiom.
def ClassifiedCubicTrees : Prop :=
  ∀ (W : Type) [Fintype W] (T : Rooted W), TreeFamily T 3 2 →
    ∃ k : Counts, Nonempty (RootedIso T (pattern k))

theorem tree_bound_of_classification (hc : ClassifiedCubicTrees) : CubicTreeBound := by
  intro W _ T hT
  obtain ⟨k,⟨e⟩⟩ := hc W T hT
  exact bound_of_iso T k e

theorem neg_conjecture_of_classification (hc : ClassifiedCubicTrees) : ¬ Conjecture2.{0} :=
  neg_conjecture_of_tree_bound (tree_bound_of_classification hc)
end EdgePattern.TreeModelsR3
'''
Path('formal/BridgeR3.lean').write_text(s)
