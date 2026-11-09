import PDTAR.ReductionTransport
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
open scoped symmDiff
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Upward closure on finite subsets, independent of power domination. -/
def ReductionUpward (P : Finset V → Prop) : Prop := ∀ ⦃S T⦄, S ⊆ T → P S → P T

/-- Flips taking one upper family onto another cannot change that family. -/
theorem reduction_flip_normalize (P Q : Finset V → Prop)
    (hp : ReductionUpward P) (hq : ReductionUpward Q) (R : Finset V)
    (h : ∀ S, P S ↔ Q (S ∆ R)) : ∀ S, P S ↔ Q S := by
  intro S
  have hd : (S ∪ R) ∆ R = S \ R := by ext x; simp only [mem_symmDiff, mem_union, mem_sdiff]; tauto
  constructor
  · intro hs
    have hpr : P (S ∪ R) := hp subset_union_left hs
    have hqr : Q (S \ R) := hd ▸ (h _).mp hpr
    exact hq sdiff_subset hqr
  · intro hs
    have hqr : Q (S ∪ R) := hq subset_union_left hs
    have hpr : P ((S ∪ R) ∆ R) := (h _).mpr (by simpa using hqr)
    exact hp (hd ▸ sdiff_subset) hpr

/-- An affine coordinate description, with an arbitrary flip mask, already suffices. -/
theorem reduction_affine_normalize (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ≃ W) (R : Finset W)
    (h : ∀ S, IsPD G S ↔ IsPD H ((S.map e.toEmbedding) ∆ R)) :
    ∀ S, IsPD G S ↔ IsPD H (S.map e.toEmbedding) := by
  have he₁ : ∀ T : Finset W, (T.map e.symm.toEmbedding).map e.toEmbedding = T := by
    intro T; ext x; simp
  have he₂ : ∀ S : Finset V, (S.map e.toEmbedding).map e.symm.toEmbedding = S := by
    intro S; ext x; simp
  have hm : ReductionUpward (fun T : Finset W => IsPD G (T.map e.symm.toEmbedding)) := by
    intro S T hst hs
    exact isPD_mono G (map_subset_map.mpr hst) hs
  have he : ∀ T : Finset W, IsPD G (T.map e.symm.toEmbedding) ↔ IsPD H (T ∆ R) := by
    intro T
    simpa only [he₁] using h (T.map e.symm.toEmbedding)
  have hn := reduction_flip_normalize _ _ hm (fun _ _ hh => isPD_mono H hh) R he
  intro S
  simpa only [he₂] using hn (S.map e.toEmbedding)
end PDTAR
