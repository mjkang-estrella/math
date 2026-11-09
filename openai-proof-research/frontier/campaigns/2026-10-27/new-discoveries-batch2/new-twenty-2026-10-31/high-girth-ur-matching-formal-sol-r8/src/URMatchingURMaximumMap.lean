module
public import URMatchingRelabel
@[expose] public section
namespace URMatching
universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]

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

end URMatching
