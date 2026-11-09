import PDTAR.ReductionCube
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
open scoped symmDiff
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem reduction_erase_injective : Function.Injective (fun v : V => (univ : Finset V).erase v) := by
  intro x y h
  by_contra hn
  have hx : x ∈ (univ : Finset V).erase y := by simp [hn]
  change univ.erase x = univ.erase y at h
  rw [← h] at hx
  simp at hx

/-- The co-singletons determine a vertex bijection, even before normalization. -/
theorem reduction_basis (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : NoIsolated G) (hH : NoIsolated H) (φ : tar G ≃g tar H) :
    ∃ e : V ≃ W, ∀ v,
      (φ ⟨univ.erase v, erase_isPD G hG v⟩).val =
        (φ ⟨univ,isPD_univ G⟩).val ∆ {e v} := by
  have hadj : ∀ v : V, (tar H).Adj (φ ⟨univ,isPD_univ G⟩)
      (φ ⟨univ.erase v,erase_isPD G hG v⟩) := by
    intro v
    apply φ.map_rel_iff.mpr
    change ((univ : Finset V) ∆ univ.erase v).card = 1
    have he : (univ : Finset V) ∆ univ.erase v = {v} := by
      ext x; simp only [mem_symmDiff, mem_univ, mem_erase, mem_singleton]; tauto
    rw [he]; simp
  have hex : ∀ v : V, ∃ w : W,
      (φ ⟨univ.erase v,erase_isPD G hG v⟩).val =
        (φ ⟨univ,isPD_univ G⟩).val ∆ {w} := by
    intro v
    exact (reduction_adj_iff_toggle _ _).mp (hadj v)
  let f : V → W := fun v => Classical.choose (hex v)
  have hf : ∀ v, (φ ⟨univ.erase v,erase_isPD G hG v⟩).val =
      (φ ⟨univ,isPD_univ G⟩).val ∆ {f v} := fun v => Classical.choose_spec (hex v)
  have hinj : Function.Injective f := by
    intro x y hxy
    have he : φ ⟨univ.erase x,erase_isPD G hG x⟩ =
        φ ⟨univ.erase y,erase_isPD G hG y⟩ := by
      apply Subtype.ext
      rw [hf x,hf y,hxy]
    have hs := congrArg Subtype.val (φ.injective he)
    exact reduction_erase_injective hs
  have hcard := reduction_card_eq G H hG hH φ
  have hsurj : Function.Surjective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩ |>.2
  exact ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,hf⟩

/-- Toggling a present coordinate decreases Hamming weight, and only then. -/
theorem reduction_toggle_card_lt (D : Finset V) (v : V) :
    (D ∆ {v}).card < D.card ↔ v ∈ D := by
  by_cases hv : v ∈ D
  · have he : D ∆ {v} = D.erase v := by
      ext x; simp only [mem_symmDiff,mem_singleton,mem_erase]; aesop
    rw [he,card_erase_of_mem hv]
    have hp : 0 < D.card := card_pos.mpr ⟨v,hv⟩
    simp only [hv, iff_true]
    omega
  · have he : D ∆ {v} = insert v D := by
      ext x; simp only [mem_symmDiff,mem_singleton,mem_insert]; aesop
    rw [he,card_insert_of_notMem hv]
    simp [hv]
end PDTAR
