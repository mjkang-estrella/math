import PDTAR.ReductionBasis
namespace PDTAR
open Finset
open scoped symmDiff

/-- Hamming-isometry specification, discharged by `reductionHammingRemaining` in ReductionPaths. -/
def ReductionHammingRemaining : Prop :=
  ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (φ : tar G ≃g tar H)
    (S T : {S : Finset V // IsPD G S}),
    ((φ S).val ∆ (φ T).val).card = (S.val ∆ T.val).card

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Completed coordinate reconstruction from the explicit metric obligation. -/
theorem reduction_affine_of_hamming (metric : ReductionHammingRemaining)
    (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : NoIsolated G) (hH : NoIsolated H) (φ : tar G ≃g tar H) :
    ∃ (e : V ≃ W) (R : Finset W), ∀ S : {S : Finset V // IsPD G S},
      (φ S).val = S.val.map e.toEmbedding ∆ R := by
  obtain ⟨e,he⟩ := reduction_basis G H hG hH φ
  let A := (φ ⟨univ,isPD_univ G⟩).val
  refine ⟨e, A ∆ univ, ?_⟩
  intro S
  ext w
  obtain ⟨v,rfl⟩ := e.surjective w
  have hm₁ := metric V W G H φ ⟨univ.erase v,erase_isPD G hG v⟩ S
  have hm₂ := metric V W G H φ ⟨univ,isPD_univ G⟩ S
  rw [he v] at hm₁
  change (A ∆ {e v} ∆ (φ S).val).card = ((univ.erase v) ∆ S.val).card at hm₁
  change (A ∆ (φ S).val).card = (univ ∆ S.val).card at hm₂
  have he₁ : A ∆ {e v} ∆ (φ S).val = (A ∆ (φ S).val) ∆ {e v} := by
    ext x; simp only [mem_symmDiff]; tauto
  have he₂ : (univ.erase v) ∆ S.val = (univ ∆ S.val) ∆ {v} := by
    ext x; simp only [mem_symmDiff,mem_erase,mem_univ,mem_singleton]; tauto
  rw [he₁,he₂] at hm₁
  have hmem : e v ∈ A ∆ (φ S).val ↔ v ∈ univ ∆ S.val := by
    rw [← reduction_toggle_card_lt, ← reduction_toggle_card_lt,hm₁,hm₂]
  simp only [mem_symmDiff,mem_univ,mem_map_equiv,Equiv.symm_apply_apply] at hmem ⊢
  change e v ∈ (φ S).val ↔ _
  tauto

/-- Surjectivity converts the affine description on feasible sets into an iff on all sets. -/
theorem reduction_affine_family (G : SimpleGraph V) (H : SimpleGraph W)
    (φ : tar G ≃g tar H) (e : V ≃ W) (R : Finset W)
    (h : ∀ S : {S : Finset V // IsPD G S}, (φ S).val = S.val.map e.toEmbedding ∆ R) :
    ∀ S, IsPD G S ↔ IsPD H (S.map e.toEmbedding ∆ R) := by
  intro S
  constructor
  · intro hs
    rw [← h ⟨S,hs⟩]
    exact (φ ⟨S,hs⟩).property
  · intro hs
    obtain ⟨T,hT⟩ := φ.surjective ⟨S.map e.toEmbedding ∆ R,hs⟩
    have hh := congrArg Subtype.val hT
    rw [h T] at hh
    have he : T.val.map e.toEmbedding = S.map e.toEmbedding := by
      have hcancel := congrArg (fun X => X ∆ R) hh
      simpa using hcancel
    have ht : T.val = S := map_injective e.toEmbedding he
    exact ht ▸ T.property
end PDTAR
