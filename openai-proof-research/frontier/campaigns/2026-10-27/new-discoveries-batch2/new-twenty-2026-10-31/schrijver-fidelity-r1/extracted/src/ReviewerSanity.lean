import Encoding
namespace Schrijver
instance smallStableDec (n : ℕ) (s : Finset (Fin n)) : Decidable (Stable n s) := by
  unfold Stable
  infer_instance
instance smallVertexFintype (n k : ℕ) : Fintype (Vertex n k) := Subtype.fintype _
instance smallAdjDec (n k : ℕ) : DecidableRel (SG n k).Adj := by
  intro a b
  change Decidable (a ≠ b ∧ Disjoint a.val b.val)
  infer_instance
example : Stable 5 ({0,2} : Finset (Fin 5)) := by decide +kernel
example : ¬ Stable 5 ({0,4} : Finset (Fin 5)) := by decide +kernel
example : ¬ Stable 5 ({1,2} : Finset (Fin 5)) := by decide +kernel
example : Stable 1 (∅ : Finset (Fin 1)) := by decide +kernel
example : ¬ Stable 1 ({0} : Finset (Fin 1)) := by decide +kernel
example : decode 5 5 = ({0,2} : Finset (Fin 5)) := by decide +kernel
example : decode 5 17 = ({0,4} : Finset (Fin 5)) := by decide +kernel
example : encode ({1,3} : Finset (Fin 5)) = 10 := by
  have h : ({1,3} : Finset (Fin 5)) = decode 5 10 := by decide +kernel
  rw [h]
  exact encode_decode (by decide)
example : validMask 5 2 5 = true ∧ validMask 5 2 17 = false := by decide +kernel
example : Fintype.card (Vertex 5 2) = 5 := by decide +kernel
private theorem small_cover : ∀ a b : Vertex 5 2,
    a = b ∨ (SG 5 2).Adj a b ∨ ∃ c, (SG 5 2).Adj a c ∧ (SG 5 2).Adj c b := by
  decide +kernel
private theorem small_walk (a b : Vertex 5 2) :
    ∃ p : (SG 5 2).Walk a b, p.length ≤ 2 := by
  rcases small_cover a b with h | h | ⟨c,hac,hcb⟩
  · subst b; exact ⟨.nil, by simp⟩
  · exact ⟨.cons h .nil, by simp⟩
  · exact ⟨.cons hac (.cons hcb .nil), by simp⟩
private def va : Vertex 5 2 := ⟨{0,2}, by decide +kernel, by decide +kernel⟩
private def vb : Vertex 5 2 := ⟨{0,3}, by decide +kernel, by decide +kernel⟩
theorem reviewer_small_connected : (SG 5 2).Connected := by
  let : Nonempty (Vertex 5 2) := ⟨va⟩
  refine ⟨?_⟩
  intro a b
  exact ⟨(small_walk a b).choose⟩
theorem reviewer_small_diameter : diam (SG 5 2) = 2 := by
  let : Nonempty (Vertex 5 2) := ⟨va⟩
  have ht := (SimpleGraph.connected_iff_ediam_ne_top (G := SG 5 2)).mp reviewer_small_connected
  have hdist : 2 ≤ (SG 5 2).dist va vb := by
    have hne : va ≠ vb := by decide +kernel
    have hna : ¬ (SG 5 2).Adj va vb := by decide +kernel
    have h0 : (SG 5 2).dist va vb ≠ 0 := by
      intro h
      exact hne ((reviewer_small_connected.dist_eq_zero_iff).mp h)
    have h1 : (SG 5 2).dist va vb ≠ 1 := by
      intro h
      exact hna (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
  have hlo := hdist.trans (SimpleGraph.dist_le_diam ht)
  let : Nonempty (Vertex 5 2) := ⟨va⟩
  obtain ⟨a,b,hab⟩ := (SG 5 2).exists_dist_eq_diam
  obtain ⟨p,hp⟩ := small_walk a b
  have hu := (SimpleGraph.dist_le p).trans hp
  change (SG 5 2).diam = 2
  omega
end Schrijver
