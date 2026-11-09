import AntimagicFinal2
import Antimagic3DepthTwo
namespace Antimagic.Round3

/-- Exact inherited formula-to-edges obligation at a specified parameter pair. -/
def FormulaConstruction (t n : ℕ) : Prop :=
  ∃ f : Labeling (tree t n),
    (∀ (u v : Vertex t n) (h : Child u v),
      (f ⟨s(u, v), (tree t n).mem_edgeSet.mpr (Or.inl h)⟩).val + 1 =
        label t n v.1.val v.2.val) ∧
    IsLocal (tree t n) f ∧ colorCount (tree t n) f = t ^ n + 1

/-- Still open: assembly of the symbolic depth-two ingredients. -/
def DepthTwoConstruction : Prop := ∀ t, 4 ≤ t → Even t → FormulaConstruction t 2

/-- Still open: the parity-shell and leaf-block construction for t >= 4. -/
def NonbinaryHigherConstruction : Prop :=
  ∀ t n, 4 ≤ t → Even t → 3 ≤ n → FormulaConstruction t n

/-- Still open: the separate binary patch, at every depth at least three. -/
def BinaryHigherConstruction : Prop := ∀ n, 3 ≤ n → FormulaConstruction 2 n

theorem remaining_iff : Round2.RemainingConstruction ↔
    DepthTwoConstruction ∧ NonbinaryHigherConstruction ∧ BinaryHigherConstruction := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro t ht he
      exact h t 2 (by omega) he (by omega) (by omega)
    · intro t n ht he hn
      exact h t n (by omega) he (by omega) (by omega)
    · intro n hn
      exact h 2 n (by omega) (by decide) (by omega) (by omega)
  · rintro ⟨d, h, b⟩ t n ht he hn hne
    have ht_cases : t = 2 ∨ 4 ≤ t := by
      obtain ⟨k, hk⟩ := he
      omega
    by_cases hn2 : n = 2
    · subst n
      exact d t (by omega) he
    · rcases ht_cases with rfl | ht4
      · exact b n (by omega)
      · exact h t n ht4 he (by omega)

/-- CONDITIONAL: all three unclosed construction subcases are explicit. -/
theorem even_case (d : DepthTwoConstruction) (h : NonbinaryHigherConstruction)
    (b : BinaryHigherConstruction) (t n : ℕ)
    (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t ^ n + 1) :=
  Round2.even_case (remaining_iff.mpr ⟨d, h, b⟩) t n ht he hn

/-- CONDITIONAL: arbitrary finite full trees also require ModelBridge. -/
theorem mathdb_354228 (d : DepthTwoConstruction) (h : NonbinaryHigherConstruction)
    (b : BinaryHigherConstruction) (bridge : ModelBridge)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n)
    (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G + 1) ∧ chiLA G = numLeaves G + 1 :=
  Round2.mathdb_354228 (remaining_iff.mpr ⟨d, h, b⟩) bridge G t n ht he hn full

#print axioms remaining_iff
#print axioms even_case
#print axioms mathdb_354228
end Antimagic.Round3
