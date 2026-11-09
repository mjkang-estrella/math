import Antimagic4AShell
namespace Antimagic.Round4A
open Round3

/-- Conditional only on the two still-open higher-depth construction families. -/
theorem even_case (h : NonbinaryHigherConstruction) (b : BinaryHigherConstruction)
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t ^ n + 1) :=
  Round3.even_case depthTwoConstruction h b t n ht he hn

/-- ModelBridge is reserved for the sibling lane and remains explicit here. -/
theorem mathdb_354228 (h : NonbinaryHigherConstruction) (b : BinaryHigherConstruction)
    (bridge : ModelBridge) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t n : ℕ)
    (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G + 1) ∧ chiLA G = numLeaves G + 1 :=
  Round3.mathdb_354228 depthTwoConstruction h b bridge G t n ht he hn full

#print axioms depthTwoConstruction
#print axioms even_case
#print axioms mathdb_354228
end Antimagic.Round4A
