import AntimagicLabel
import AntimagicIso
namespace Antimagic

/-- The missing graph-incidence lower bound, for all labels, including odd t. -/
def LowerBound : Prop := ∀ t n, 2 ≤ t → 1 ≤ n →
  ∀ f : Labeling (tree t n), IsLocal (tree t n) f →
    t ^ n + 1 ≤ colorCount (tree t n) f

/-- The missing construction-to-edges theorem: it must exhibit the explicit
formula, via an edge/lower-endpoint equivalence, not an unrelated labelling. -/
def Construction : Prop := ∀ t n, 2 ≤ t → Even t → 1 ≤ n →
  ∃ (f : Labeling (tree t n)),
    (∀ (u v : Vertex t n) (h : Child u v),
      (f ⟨s(u, v), (tree t n).mem_edgeSet.mpr (Or.inl h)⟩).val + 1 =
        label t n v.1.val v.2.val) ∧
    IsLocal (tree t n) f ∧ colorCount (tree t n) f = t ^ n + 1

/-- Proved isomorphism invariance, including degree-one leaf count. -/
theorem iso_invariant {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) :
    spectrum G = spectrum H ∧ numLeaves G = numLeaves H :=
  ⟨spectrum_iso e, leaves_iso e⟩

/-- CONDITIONAL endpoint: no claim that either obligation is discharged. -/
theorem even_case (lower : LowerBound) (construction : Construction)
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n) :
    IsLeast (spectrum (tree t n)) (t ^ n + 1) := by
  obtain ⟨f, _, hf, hc⟩ := construction t n ht he hn
  exact least_of_bounds _ _ ⟨f, hf, hc⟩ (lower t n ht hn)

/-- CONDITIONAL full-scope MathDB endpoint; arbitrary finite source trees. -/
theorem mathdb_354228 (lower : LowerBound) (construction : Construction)
    (bridge : ModelBridge) (leaves : ModelLeaves)
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t n : ℕ) (ht : 2 ≤ t) (he : Even t) (hn : 1 ≤ n)
    (full : FullTree G t n) :
    IsLeast (spectrum G) (numLeaves G + 1) ∧ chiLA G = numLeaves G + 1 := by
  obtain ⟨e⟩ := bridge V G t n ht hn full
  obtain ⟨hs, hl⟩ := iso_invariant G (tree t n) e
  have h := even_case lower construction t n ht he hn
  rw [← hs, ← leaves t n ht hn, ← hl] at h
  exact ⟨h, chiLA_eq_of_least G h⟩

#print axioms even_case
#print axioms mathdb_354228
end Antimagic
