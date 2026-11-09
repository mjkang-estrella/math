import Antimagic4BBridge
import AntimagicFinal3

namespace Antimagic.Round4B
/-- Every source FullTree is isomorphic to the literal frozen row-index model. -/
theorem modelBridge : ModelBridge := by
  intro V _ _ G _ t n ht hn S
  obtain ⟨T, _, _, _⟩ := modelStructure t n ht hn
  exact ⟨fullTreeIso S T⟩


/-- Conditional only on the three construction obligations assigned to Round 4A. -/
theorem mathdb_354228 (d : Round3.DepthTwoConstruction)
    (h : Round3.NonbinaryHigherConstruction) (b : Round3.BinaryHigherConstruction)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n)
    (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G + 1) ∧ chiLA G = numLeaves G + 1 :=
  Round3.mathdb_354228 d h b modelBridge G t n ht he hn full

#print axioms modelBridge
#print axioms mathdb_354228
end Antimagic.Round4B
