import Antimagic5ABijection
import AntimagicFinal4A
namespace Antimagic.Round5A
open Round3

/-- Exact residual nonbinary obligation: properness and colour count of the
literal edge equivalence already constructed in this round. This is a Prop,
not an assertion that these properties have been proved. -/
def NonbinaryWeightCompletion : Prop := ∀ s n (hs : 2 ≤ s) (hn : 3 ≤ n),
  IsLocal (tree (2*s) n) (higherLabeling s n hs hn) ∧
    colorCount (tree (2*s) n) (higherLabeling s n hs hn) = (2*s)^n+1

theorem nonbinaryHigherConstruction_of_weights (weights : NonbinaryWeightCompletion) :
    NonbinaryHigherConstruction := by
  intro t n ht he hn
  obtain ⟨s,hs⟩ := he
  have ht2 : t = 2*s := by omega
  clear hs
  subst t
  have hs2 : 2 ≤ s := by omega
  refine ⟨higherLabeling s n hs2 hn,?_,(weights s n hs2 hn).1,(weights s n hs2 hn).2⟩
  intro u v h
  let a : Nonroot (2*s) n := ⟨v,by have := h.1; unfold depth; omega⟩
  have heq : (⟨s(u,v),(tree (2*s) n).mem_edgeSet.mpr (Or.inl h)⟩ : (tree (2*s) n).edgeSet) = incomingEdge (by omega) a := by
    apply Subtype.ext
    change s(u,v) = s(parent (by omega) a,v)
    rw [← child_parent_unique h (by omega)]
  rw [heq]
  exact higherLabeling_label s n hs2 hn a

/-- Conditional endpoint: the remaining nonbinary weight obligation and binary
higher-depth construction are explicit. -/
theorem even_case (weights : NonbinaryWeightCompletion) (binary : BinaryHigherConstruction)
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t^n+1) :=
  Round4A.even_case (nonbinaryHigherConstruction_of_weights weights) binary t n ht he hn

theorem mathdb_354228 (weights : NonbinaryWeightCompletion) (binary : BinaryHigherConstruction)
    (bridge : ModelBridge) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t n : ℕ)
    (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G+1) ∧ chiLA G = numLeaves G+1 :=
  Round4A.mathdb_354228 (nonbinaryHigherConstruction_of_weights weights) binary bridge G t n ht he hn full

#print axioms nonbinaryHigherConstruction_of_weights
#print axioms even_case
#print axioms mathdb_354228
end Antimagic.Round5A
