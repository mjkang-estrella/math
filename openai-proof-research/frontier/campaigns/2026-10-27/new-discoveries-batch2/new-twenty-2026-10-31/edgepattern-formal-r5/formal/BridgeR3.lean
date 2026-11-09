import EvalR3_0000
import EvalR3_0001
import EvalR3_0002
import EvalR3_0010
import EvalR3_0011
import EvalR3_0012
import EvalR3_0020
import EvalR3_0021
import EvalR3_0022
import EvalR3_0100
import EvalR3_0101
import EvalR3_0102
import EvalR3_0110
import EvalR3_0111
import EvalR3_0112
import EvalR3_0120
import EvalR3_0121
import EvalR3_0122
import EvalR3_0200
import EvalR3_0201
import EvalR3_0202
import EvalR3_0210
import EvalR3_0211
import EvalR3_0212
import EvalR3_0220
import EvalR3_0221
import EvalR3_0222
import EvalR3_1000
import EvalR3_1001
import EvalR3_1002
import EvalR3_1010
import EvalR3_1011
import EvalR3_1012
import EvalR3_1020
import EvalR3_1021
import EvalR3_1022
import EvalR3_1100
import EvalR3_1101
import EvalR3_1102
import EvalR3_1110
import EvalR3_1111
import EvalR3_1112
import EvalR3_1120
import EvalR3_1121
import EvalR3_1122
import EvalR3_1200
import EvalR3_1201
import EvalR3_1202
import EvalR3_1210
import EvalR3_1211
import EvalR3_1212
import EvalR3_1220
import EvalR3_1221
import EvalR3_1222
import EvalR3_2000
import EvalR3_2001
import EvalR3_2002
import EvalR3_2010
import EvalR3_2011
import EvalR3_2012
import EvalR3_2020
import EvalR3_2021
import EvalR3_2022
import EvalR3_2100
import EvalR3_2101
import EvalR3_2102
import EvalR3_2110
import EvalR3_2111
import EvalR3_2112
import EvalR3_2120
import EvalR3_2121
import EvalR3_2122
import EvalR3_2200
import EvalR3_2201
import EvalR3_2202
import EvalR3_2210
import EvalR3_2211
import EvalR3_2212
import EvalR3_2220
import EvalR3_2221
import EvalR3_2222
import InvarianceR2
import ReductionR2
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem all_81 (k : Counts) :
    1 ≤ ∑ i : Fin 3, Concrete.alpha i * expectation (pattern k) i := by
  simp_rw [expectation_eq]
  obtain ⟨a,b,c,d⟩ := k
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact bound_0000
  · exact bound_0001
  · exact bound_0002
  · exact bound_0010
  · exact bound_0011
  · exact bound_0012
  · exact bound_0020
  · exact bound_0021
  · exact bound_0022
  · exact bound_0100
  · exact bound_0101
  · exact bound_0102
  · exact bound_0110
  · exact bound_0111
  · exact bound_0112
  · exact bound_0120
  · exact bound_0121
  · exact bound_0122
  · exact bound_0200
  · exact bound_0201
  · exact bound_0202
  · exact bound_0210
  · exact bound_0211
  · exact bound_0212
  · exact bound_0220
  · exact bound_0221
  · exact bound_0222
  · exact bound_1000
  · exact bound_1001
  · exact bound_1002
  · exact bound_1010
  · exact bound_1011
  · exact bound_1012
  · exact bound_1020
  · exact bound_1021
  · exact bound_1022
  · exact bound_1100
  · exact bound_1101
  · exact bound_1102
  · exact bound_1110
  · exact bound_1111
  · exact bound_1112
  · exact bound_1120
  · exact bound_1121
  · exact bound_1122
  · exact bound_1200
  · exact bound_1201
  · exact bound_1202
  · exact bound_1210
  · exact bound_1211
  · exact bound_1212
  · exact bound_1220
  · exact bound_1221
  · exact bound_1222
  · exact bound_2000
  · exact bound_2001
  · exact bound_2002
  · exact bound_2010
  · exact bound_2011
  · exact bound_2012
  · exact bound_2020
  · exact bound_2021
  · exact bound_2022
  · exact bound_2100
  · exact bound_2101
  · exact bound_2102
  · exact bound_2110
  · exact bound_2111
  · exact bound_2112
  · exact bound_2120
  · exact bound_2121
  · exact bound_2122
  · exact bound_2200
  · exact bound_2201
  · exact bound_2202
  · exact bound_2210
  · exact bound_2211
  · exact bound_2212
  · exact bound_2220
  · exact bound_2221
  · exact bound_2222

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
