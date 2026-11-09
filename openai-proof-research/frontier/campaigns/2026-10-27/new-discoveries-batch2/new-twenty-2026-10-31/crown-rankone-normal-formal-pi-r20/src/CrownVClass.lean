import CrownVCount
import Mathlib.Data.Fintype.Sum

/-!
Cut sets of the crown graph (paper Definition 2.2) and the first structural
lemmas of the classification.

`VCut S t` says that `t` is a cut vertex of the induced graph on `S ∪ {t}` in
the standard path form: two vertices of `S` are connected in `S ∪ {t}` but not
in `S` alone.  For `t ∉ S` this is equivalent to the component-count form
(c(H - t) > c(H)): a splitting component gives two such vertices, and two such
vertices split their common component, raising the count by at least one,
while removing one vertex never merges components.

`Cutset T` is paper Definition 2.2: `T = ∅`, or every `t ∈ T` is a cut vertex
of the graph induced on `(V ∖ T) ∪ {t}`.

`sameC_eq_or_step` is the basic refutation tool for non-connectivity: a
nontrivial path has a first edge.
-/

namespace CrownV

variable {n : ℕ}

/-- A nontrivial path has a first edge. -/
theorem sameC_eq_or_step {s : Finset (V n)} {x y : V n} (h : SameC s x y) :
    x = y ∨ ∃ w, SEdge s x w ∧ SameC s w y :=
  Relation.ReflTransGen.cases_head h

/-- If no edge of `s` leaves `x`, every path from `x` is trivial. -/
theorem sameC_eq_of_forall_not_sEdge {s : Finset (V n)} {x y : V n}
    (hno : ∀ w, ¬ SEdge s x w) (h : SameC s x y) : x = y := by
  rcases sameC_eq_or_step h with he | ⟨w, hw, _⟩
  · exact he
  · exact absurd hw (hno w)

/-- `t` is a cut vertex of the graph induced on `S ∪ {t}` (path form). -/
def VCut (S : Finset (V n)) (t : V n) : Prop :=
  ∃ x y, x ∈ S ∧ y ∈ S ∧ SameC (insert t S) x y ∧ ¬ SameC S x y

/-- Paper Definition 2.2: `T = ∅`, or every `t ∈ T` is a cut vertex of the
graph induced on `(V ∖ T) ∪ {t}`. -/
def Cutset (T : Finset (V n)) : Prop :=
  T = ∅ ∨ ∀ t ∈ T, VCut ((Finset.univ : Finset (V n)) \ T) t

end CrownV
