import Sigma.Structure
import Sigma.Attainment

namespace Sigma365710
open Finset

theorem sum_membership {n : ℕ} (S : Finset (Fin n)) (x y : ℤ) :
    (∑ u : Fin n, if u ∈ S then x else y) =
      (S.card : ℤ) * x + ((n : ℤ) - S.card) * y := by
  rw [sum_ite]
  have he : univ.filter (fun u => u ∈ S) = S := by ext; simp
  have hn : (univ.filter (fun u => u ∉ S)).card = n - S.card := by
    have h := card_filter_add_card_filter_not (p := fun u => u ∈ S) (s := univ)
    rw [he] at h
    simp only [card_univ,Fintype.card_fin] at h
    omega
  have hle : S.card ≤ n := by simpa using card_le_card (subset_univ S)
  simp only [sum_const, nsmul_eq_mul, he, hn, Nat.cast_sub hle]

theorem bipartition_value {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hc : G.Connected) (hb : HasCompleteBipartition G) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ sigmaT G = F n k := by
  classical
  obtain ⟨A,hA⟩ := hb
  let S := A.toFinset
  have hs : ∀ u, u ∈ S ↔ u ∈ A := fun _ => Set.mem_toFinset
  have hAdj : ∀ u v, G.Adj u v ↔ (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S) := by
    intro u v
    simpa only [hs] using hA u v
  have hdeg : ∀ u, G.degree u = if u ∈ S then n - S.card else S.card := by
    intro u
    rw [← G.card_neighborFinset_eq_degree]
    by_cases hu : u ∈ S
    · have he : G.neighborFinset u = univ \ S := by
        ext v; simp [hAdj,hu]
      rw [he,card_sdiff_of_subset (subset_univ S)]
      simp [hu]
    · have he : G.neighborFinset u = S := by ext v; simp [hAdj,hu]
      simp [he,hu]
  have : Nontrivial (Fin n) := ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro h; have := congrArg Fin.val h; simp at this⟩⟩
  let z : Fin n := ⟨0,by omega⟩
  obtain ⟨v,hzv⟩ := hc.preconnected.exists_adj_of_nontrivial z
  have hboth : S.Nonempty ∧ (univ \ S).Nonempty := by
    rcases (hAdj z v).mp hzv with h | h
    · exact ⟨⟨z,h.1⟩,⟨v,by simp [h.2]⟩⟩
    · exact ⟨⟨v,h.2⟩,⟨z,by simp [h.1]⟩⟩
  have hpos := card_pos.mpr hboth.1
  have hcompl := card_pos.mpr hboth.2
  rw [card_sdiff_of_subset (subset_univ S),card_univ,Fintype.card_fin] at hcompl
  have hlt : S.card < n := by omega
  refine ⟨S.card,by omega,hlt,?_⟩
  rw [sigmaT,pair_variance]
  simp_rw [hdeg]
  push_cast
  simp only [ite_pow]
  rw [sum_membership,sum_membership,Nat.cast_sub hlt.le]
  unfold F
  ring

end Sigma365710
