module
public import URMatchingRelabel
@[expose] public section
namespace URMatching
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]

theorem matchingNumber_equiv {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hg : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)) :
    matchingNumber G = matchingNumber H := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨M,hm,he⟩ := exists_maximum_matching G
    have h := card_le_matchingNumber H (mapped_matching e e.injective (fun x y h => (hg x y).mp h) hm)
    rwa [mappedEdges_card,he] at h
  · obtain ⟨M,hm,he⟩ := exists_maximum_matching H
    have h := card_le_matchingNumber G (mapped_matching e.symm e.symm.injective
      (fun x y h => (hg (e.symm x) (e.symm y)).mpr (by simpa using h)) hm)
    rwa [mappedEdges_card,he] at h

theorem urMatchingNumber_equiv {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (hg : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)) :
    urMatchingNumber G = urMatchingNumber H := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨M,hm,he⟩ := exists_maximum_urMatching G
    have h := card_le_urMatchingNumber H (mapped_ur e hg hm)
    rwa [mappedEdges_card,he] at h
  · obtain ⟨M,hm,he⟩ := exists_maximum_urMatching H
    have h := card_le_urMatchingNumber G (mapped_ur e.symm
      (fun x y => by simpa using (hg (e.symm x) (e.symm y)).symm) hm)
    rwa [mappedEdges_card,he] at h

def pullbackGraph (e : V ≃ W) (H : SimpleGraph W) : SimpleGraph V where
  Adj x y := H.Adj (e x) (e y)
  symm := ⟨fun _ _ h => H.adj_symm h⟩
  loopless := ⟨fun x => H.loopless.irrefl (e x)⟩

theorem canonical_matching_numbers (G : SimpleGraph V) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), matchingNumber H = matchingNumber G ∧
      urMatchingNumber H = urMatchingNumber G := by
  classical
  let e := (Fintype.equivFin V).symm
  let H := pullbackGraph e G
  exact ⟨H,matchingNumber_equiv e (fun _ _ => Iff.rfl),
    urMatchingNumber_equiv e (fun _ _ => Iff.rfl)⟩
end URMatching
