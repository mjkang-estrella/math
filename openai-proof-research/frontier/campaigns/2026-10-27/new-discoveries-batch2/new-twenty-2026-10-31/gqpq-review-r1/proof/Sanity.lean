import Endpoint
open Cover377831
example : ContainsSGQPQ (Finset.univ : Finset (Point 1)) Finset.univ := by
  refine ⟨1, (fun a _ => some a), id, ?_⟩
  decide
example : ContainsSGQPQ (∅ : Finset (Point 3)) ∅ := by
  refine ⟨3, (fun _ _ => none), id, ?_⟩
  decide
example : (Finset.univ : Finset (Line 3)).card = 27 := by decide
example : H.card = 17 := by decide
example : ¬ ContainsSGQPQ H Finset.univ := no_partial_quotient
example : ¬ SourceConjecture := source_refutation
