import G2
namespace Bicir
open Relation
variable {g : Gr}
-- probe: is union-membership defeq-acceptable for goal `x ∈ uu`?
example (F : Finset (Fin g.m)) (e : Fin g.m) (x : Fin g.v)
    (h : x ∈ cmp g F (g.ep e).1) : x ∈ uu g F e := by
  have : x ∈ cmp g F (g.ep e).1 ∪ cmp g F (g.ep e).2 := Finset.mem_union.mpr (Or.inl h)
  exact this
end Bicir
