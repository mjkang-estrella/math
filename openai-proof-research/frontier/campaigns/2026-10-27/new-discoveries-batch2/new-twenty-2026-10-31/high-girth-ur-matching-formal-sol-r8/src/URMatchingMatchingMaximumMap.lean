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

end URMatching
