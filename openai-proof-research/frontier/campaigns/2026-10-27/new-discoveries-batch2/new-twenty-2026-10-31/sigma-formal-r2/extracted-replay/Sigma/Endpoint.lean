import Sigma.Gap
import Sigma.Bracketing
import Sigma.BipartitionValue

namespace Sigma365710
open Finset

theorem non_completeBipartition_order {n : ℕ} (G : SimpleGraph (Fin n))
    (hc : G.Connected) (ht : G.CliqueFree 3) (hb : ¬ HasCompleteBipartition G) : 4 ≤ n := by
  classical
  obtain ⟨a,b,c,d,hp⟩ := inducedP4_of_not_completeBipartition G hc ht hb
  rcases hp with ⟨hab,hac,had,hbc,hbd,hcd,_⟩
  have hcard : ({a,b,c,d} : Finset (Fin n)).card = 4 := by simp [hab,hac,had,hbc,hbd,hcd]
  have hle := card_le_card (subset_univ ({a,b,c,d} : Finset (Fin n)))
  simpa [hcard] using hle

theorem non_completeBipartition_strict {n a : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hc : G.Connected) (ht : G.CliqueFree 3)
    (hb : ¬ HasCompleteBipartition G)
    (hmax : ∀ b : ℕ, 1 ≤ b → b < n → F n b ≤ F n a) : sigmaT G < F n a := by
  have hn := non_completeBipartition_order G hc ht hb
  have hgap := non_completeBipartition_deficit_gap G hc ht hb
  have hcap : 16 * sigmaT G ≤ (n : ℤ)^4 - 16 * (n : ℤ) * ((n : ℤ)-2) := by
    rw [sigmaT_deficit_identity]
    have hs := sq_nonneg (8 * edgeCount G - (n : ℤ)^2)
    have hm := mul_nonneg (show (0 : ℤ) ≤ n by omega)
      (sub_nonneg.mpr hgap)
    nlinarith
  by_cases hlarge : 7 ≤ n
  · obtain ⟨b,hb1,hbn,hbr⟩ := exists_bracketing_part hlarge
    have hba := hmax b hb1 hbn
    have hnz : (7 : ℤ) ≤ n := by exact_mod_cast hlarge
    nlinarith
  · have hstar := hmax 1 (by omega) (by omega)
    have hcases : n = 4 ∨ n = 5 ∨ n = 6 := by omega
    rcases hcases with h | h | h <;> subst n <;> norm_num [F] at hcap hstar ⊢ <;> omega

/-- Literal universal domination, for every maximizing part size. -/
theorem extremal_completeBipartite {n a : ℕ} (hn : 2 ≤ n) (ha : 1 ≤ a) (han : a < n)
    (hmax : ∀ b : ℕ, 1 ≤ b → b < n → F n b ≤ F n a) :
    (completeBipartite n a).Connected ∧ (completeBipartite n a).CliqueFree 3 ∧
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Connected → G.CliqueFree 3 → sigmaT G ≤ sigmaT (completeBipartite n a) := by
  refine ⟨completeBipartite_connected ha han,completeBipartite_cliqueFree n a,?_⟩
  intro G _ hc ht
  rw [completeBipartite_sigmaT han]
  by_cases hb : HasCompleteBipartition G
  · obtain ⟨k,hk,hkn,hval⟩ := bipartition_value hn G hc hb
    rw [hval]
    exact hmax k hk hkn
  · exact (non_completeBipartition_strict G hc ht hb hmax).le

/-- Every connected triangle-free attainer has complementary independent parts
with every cross pair adjacent, with both parts nonempty. -/
theorem attainer_classification {n a : ℕ} (hn : 2 ≤ n) (han : a < n)
    (hmax : ∀ b : ℕ, 1 ≤ b → b < n → F n b ≤ F n a)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hc : G.Connected)
    (ht : G.CliqueFree 3) (heq : sigmaT G = sigmaT (completeBipartite n a)) :
    ∃ S : Set (Fin n), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ∀ u v, G.Adj u v ↔ (u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S) := by
  classical
  have hb : HasCompleteBipartition G := by
    by_contra hb
    have hs := non_completeBipartition_strict G hc ht hb hmax
    rw [heq,completeBipartite_sigmaT han] at hs
    exact (lt_irrefl _ hs)
  obtain ⟨S,hS⟩ := hb
  have : Nontrivial (Fin n) := ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro h; have := congrArg Fin.val h; simp at this⟩⟩
  let z : Fin n := ⟨0,by omega⟩
  obtain ⟨v,hzv⟩ := hc.preconnected.exists_adj_of_nontrivial z
  rcases (hS z v).mp hzv with h | h
  · exact ⟨S,⟨z,h.1⟩,⟨v,h.2⟩,hS⟩
  · exact ⟨S,⟨v,h.2⟩,⟨z,h.1⟩,hS⟩

/-- The existential endpoint requested in the source review. -/
theorem mathdb_365710 {n : ℕ} (hn : 2 ≤ n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < n ∧
      (∀ b : ℕ, 1 ≤ b → b < n → F n b ≤ F n a) ∧
      (completeBipartite n a).Connected ∧ (completeBipartite n a).CliqueFree 3 ∧
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → G.CliqueFree 3 → sigmaT G ≤ F n a := by
  obtain ⟨a,ha,han,hmax⟩ := exists_maximizing_part hn
  obtain ⟨hc,ht,hbound⟩ := extremal_completeBipartite hn ha han hmax
  refine ⟨a,ha,han,hmax,hc,ht,?_⟩
  intro G _ hgc hgt
  simpa only [completeBipartite_sigmaT han] using hbound G hgc hgt

end Sigma365710
