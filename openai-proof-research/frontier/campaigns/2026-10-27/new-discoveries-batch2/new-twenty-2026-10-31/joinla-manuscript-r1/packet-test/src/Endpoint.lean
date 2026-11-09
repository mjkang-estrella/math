import LauShiu

open Antimagic

def Conjecture41 : Prop := ∀ r s m : ℕ, 1 ≤ r → 1 ≤ s → 2 ≤ m →
 chiLA (LauShiu.graph r s m) = 3

namespace LauShiu

theorem three_of_colorCount (f : Labeling (graph 1 1 2)) (hc : colorCount (graph 1 1 2) f = 3) :
 R159.Three (indexedLabel f) := by
 classical
 obtain ⟨a,b,c,_,_,_,hp⟩ := Finset.card_eq_three.mp hc
 refine ⟨(a:ℤ),(b:ℤ),(c:ℤ), ?_⟩
 intro v
 have hm : weight (graph 1 1 2) f (vertexMap v) ∈
     Finset.univ.image (weight (graph 1 1 2) f) := Finset.mem_image.mpr ⟨vertexMap v, Finset.mem_univ _, rfl⟩
 rw [hp] at hm
 simp only [Finset.mem_insert, Finset.mem_singleton] at hm
 rw [weight_correspondence]
 rcases hm with h|h|h
 · exact Or.inl (congrArg (fun n : ℕ => (n:ℤ)) h)
 · exact Or.inr (Or.inl (congrArg (fun n : ℕ => (n:ℤ)) h))
 · exact Or.inr (Or.inr (congrArg (fun n : ℕ => (n:ℤ)) h))

theorem proper_transport (f : Labeling (graph 1 1 2)) (hf : IsLocal (graph 1 1 2) f) :
 R159.Proper (indexedLabel f) := by
 intro e h
 apply hf (vertexMap (R159.ends e).1) (vertexMap (R159.ends e).2)
   ((adj_correspondence _ _).mpr ((R159.edge_complete _ _).mpr ⟨e, Or.inl ⟨rfl,rfl⟩⟩))
 have hh := h
 rw [weight_correspondence, weight_correspondence] at hh
 exact_mod_cast hh

theorem instance_chi_ne_three : chiLA (graph 1 1 2) ≠ 3 := by
 intro h
 have hn : (spectrum (graph 1 1 2)).Nonempty := by
   by_contra he
   have hempty := Set.not_nonempty_iff_eq_empty.mp he
   unfold chiLA at h
   rw [hempty, Nat.sInf_empty] at h
   contradiction
 have hm := Nat.sInf_mem hn
 change chiLA (graph 1 1 2) ∈ spectrum (graph 1 1 2) at hm
 rw [h] at hm
 obtain ⟨f,hf,hc⟩ := hm
 exact R159.no_three (indexedLabel f) (indexed_labeling f) (proper_transport f hf) (three_of_colorCount f hc)
end LauShiu

theorem not_conjecture41 : ¬ Conjecture41 := by
 intro h
 exact LauShiu.instance_chi_ne_three (h 1 1 2 (by omega) (by omega) (by omega))

#print axioms not_conjecture41
