import StackSortDel5Bounds
import StackSortFinal4
namespace StackSort.Del5
open Seeds2 Round4

/-- The deletion equivalence identifies the two actual domains before counting. -/
theorem deletion_card (m r s : ℕ) :
    Nat.card (ReducedPairs m r s) = Nat.card (MaximumPairs m r s) :=
  Nat.card_congr (deletionEquiv m r s)

/-- Fixed-maximum final-block counting remains to be assembled. -/
def FixedMaximumDecomposition : Prop := ∀ M r s, 1 ≤ M →
    1 ≤ r → r ≤ bound M → 1 ≤ s → s ≤ bound M →
    Nat.card (MaximumPairs (M-1) r s) =
      literalI M r s + correction true literalX literalI M r s

/-- The finite arity sum remains; clipping has already been proved separately. -/
def TaggedDeletionCount : Prop := ∀ M r s, 1 ≤ M →
    1 ≤ r → r ≤ bound M → 1 ≤ s → s ≤ bound M →
    Nat.card (ReducedPairs (M-1) r s) = deletion XI M r s

/-- Conditional endpoint, with the two remaining counts explicit. -/
theorem maximumFinalCount_of_bridges (hf : FixedMaximumDecomposition)
    (hd : TaggedDeletionCount) : Round3.MaximumFinalCount := by
  intro M r s hM hr hrB hs hsB
  exact (hf M r s hM hr hrB hs hsB).symm.trans
    ((deletion_card (M-1) r s).symm.trans
      ((hd M r s hM hr hrB hs hsB).trans
        (deletion_eq_raw M r s hM hr hs hrB hsB).symm))

/-- Regression: a unary suffix has two distinct root insertions. -/
theorem unary_multiplicity (w : {w : List ℕ // w ≠ []}) :
    (childChoices [w.val]).card = 2 := by
  simpa [mu] using childChoices_card
    (F := [w.val]) (by simpa [NonemptyWords] using w.property) (by simp)

/-- Regression: deleting a leaf does not force the remaining tuple to be nonempty. -/
theorem empty_reconstruction :
    [] ++ [rootWord 0 Children.leaf.parts] ∈ tuples 1 1 ∧
      (output ([] ++ [rootWord 0 Children.leaf.parts])).idxOf 0 + 1 = 1 := by
  apply representation_maximum_final (c := .leaf) (A := [])
  rw [mem_tuples]
  simp [childrenTuple,childrenArity,mem_words]
end StackSort.Del5
#print axioms StackSort.Del5.deletionEquiv
#print axioms StackSort.Del5.deletion_card
#print axioms StackSort.Del5.maximumFinalCount_of_bridges
