import Antimagic6ABinaryWeights
namespace Antimagic.Round6A

/-- Round 6A closes the nonbinary construction. The binary higher-depth
construction is the sole remaining model-construction hypothesis. -/
theorem even_case (binary : Round3.BinaryHigherConstruction)
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t^n+1) :=
  Round4A.even_case nonbinaryHigherConstruction binary t n ht he hn

/-- Conditional arbitrary-tree endpoint: the binary construction and model
bridge remain explicit. This is not an unconditional resolution. -/
theorem mathdb_354228 (binary : Round3.BinaryHigherConstruction) (bridge : ModelBridge)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G+1) ∧ chiLA G=numLeaves G+1 :=
  Round4A.mathdb_354228 nonbinaryHigherConstruction binary bridge G t n ht he hn full

#print axioms nonbinaryWeightCompletion
#print axioms nonbinaryHigherConstruction
#print axioms even_case
#print axioms mathdb_354228
end Antimagic.Round6A
