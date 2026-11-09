import PDTAR.CoreSmallProof
namespace PDTAR
open Finset
-- EXPECTED FAILURE: the cross-degree theorem cannot drop its (3,3) exclusion.
example {V : Type} [Fintype V] [DecidableEq V] {K H : SimpleGraph V} {A B : Finset V}
    (hk : CompleteBetween K A B) (he : SamePD K H)
    (ha : 3 ≤ A.card) (hb : 3 ≤ B.card) {a : V} (haA : a ∈ A) :
    ∃ b ∈ B, ∃ c ∈ B, b ≠ c ∧ H.Adj a b ∧ H.Adj a c := by
  exact core_cross_two hk he ha hb haA
end PDTAR
