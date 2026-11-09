import Hierarchy
open Supervenience
example (W : Type) (M : Model W) (w : W) : eval M (gate (.atom 0) (.atom 1)) w ↔ ∀ u v, M.edge w u v → M.val u 0 → M.val v 0 → (M.val u 1 ↔ M.val v 1) := gate_eval M _ _ w
example : ¬ StrictStep 1 := hierarchy_conjecture_false
example (W : Type) (M : Model W) (f : Form 2) : ∀ w, eval M (translate f) w ↔ eval M f w := translate_correct M f
example : ¬ HierarchyConjecture := literal_conjecture_false
