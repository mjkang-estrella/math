import AntimagicBasics
namespace Antimagic
open Finset
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

def transport (e : G ≃g H) (f : Labeling G) : Labeling H :=
  e.mapEdgeSet.symm.trans (f.trans (finCongr (Fintype.card_congr e.mapEdgeSet)))

theorem weight_transport (e : G ≃g H) (f : Labeling G) (v : V) :
    weight H (transport e f) (e v) = weight G f v := by
  unfold weight
  rw [← e.mapEdgeSet.sum_comp]
  apply sum_congr rfl
  intro a _
  have hm : e v ∈ (e.mapEdgeSet a).val ↔ v ∈ a.val := by
    change e v ∈ Sym2.map e a.val ↔ v ∈ a.val
    simp only [Sym2.mem_map]
    constructor
    · rintro ⟨b, hb, he⟩
      have : b = v := e.injective he
      simpa [this] using hb
    · intro hv; exact ⟨v, hv, rfl⟩
  simp only [hm, transport, Equiv.trans_apply, Equiv.symm_apply_apply, finCongr_apply, Fin.val_cast]

theorem local_transport (e : G ≃g H) (f : Labeling G) (hf : IsLocal G f) :
    IsLocal H (transport e f) := by
  intro u v huv
  obtain ⟨a, rfl⟩ := e.surjective u
  obtain ⟨b, rfl⟩ := e.surjective v
  rw [weight_transport, weight_transport]
  exact hf a b (e.map_rel_iff.mp huv)

theorem count_transport (e : G ≃g H) (f : Labeling G) :
    colorCount H (transport e f) = colorCount G f := by
  classical
  unfold colorCount
  congr 1
  ext a
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := e.surjective v
    exact ⟨u, (weight_transport e f u).symm.trans hv⟩
  · rintro ⟨u, hu⟩
    exact ⟨e u, (weight_transport e f u).trans hu⟩

theorem spectrum_iso (e : G ≃g H) : spectrum G = spectrum H := by
  ext k
  constructor
  · rintro ⟨f, hf, hc⟩
    exact ⟨transport e f, local_transport e f hf, (count_transport e f).trans hc⟩
  · rintro ⟨f, hf, hc⟩
    exact ⟨transport e.symm f, local_transport e.symm f hf,
      (count_transport e.symm f).trans hc⟩

omit [DecidableEq V] [DecidableEq W] in
theorem leaves_iso (e : G ≃g H) : numLeaves G = numLeaves H := by
  classical
  unfold numLeaves
  apply card_equiv e.toEquiv
  intro v
  simp only [mem_filter, mem_univ, true_and]
  change G.degree v = 1 ↔ H.degree (e v) = 1
  rw [e.degree_eq]

theorem chiLA_iso (e : G ≃g H) : chiLA G = chiLA H := by
  unfold chiLA
  rw [spectrum_iso e]
end Antimagic
