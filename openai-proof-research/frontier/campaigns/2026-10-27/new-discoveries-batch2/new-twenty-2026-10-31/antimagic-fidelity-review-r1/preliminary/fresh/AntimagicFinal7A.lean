import Antimagic7AConstruction
import AntimagicFinal6A
import AntimagicFinal4B
namespace Antimagic.Round7A

theorem even_case (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t^n+1) :=
  Round6A.even_case binaryHigherConstruction t n ht he hn

theorem mathdb_354228
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G+1) ∧ chiLA G=numLeaves G+1 :=
  Round6A.mathdb_354228 binaryHigherConstruction Round4B.modelBridge G t n ht he hn full

#print axioms even_case
#print axioms mathdb_354228
end Antimagic.Round7A
