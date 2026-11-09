import GirthR2
import Separation
namespace EdgePattern
open scoped BigOperators

-- The remaining universal obligation is explicit, and is not postulated as an axiom.
def CubicTreeBound : Prop :=
  ∀ (V : Type) [Fintype V] (T : Rooted V), TreeFamily T 3 2 →
    1 ≤ ∑ i : Fin 3, Concrete.alpha i * expectation T i

theorem neg_conjecture_of_tree_bound (bound : CubicTreeBound) : ¬ Conjecture2.{0} := by
  intro hc
  obtain ⟨m,W,f,T,w,hT,hw,hs,hweak⟩ :=
    hc 3 2 (by decide) (by decide) Concrete.V Concrete.pattern
      Concrete.regular Concrete.exact_girth
  have hp : (∑ i : Fin 3, (Concrete.alpha i : ℝ) * (expectation Concrete.pattern i : ℝ)) < 1 := by
    exact_mod_cast Concrete.expectation_separating_lt_one
  have ht : ∀ j, 1 ≤ ∑ i : Fin 3, (Concrete.alpha i : ℝ) *
      (@expectation (W j) (f j) (T j) i : ℝ) := by
    intro j
    have hb := @bound (W j) (f j) (T j) (hT j)
    exact_mod_cast hb
  exact finite_separation Concrete.alpha _ _ w Concrete.alpha_positive hp ht
    (fun j => (hw j).1) hs hweak
end EdgePattern
