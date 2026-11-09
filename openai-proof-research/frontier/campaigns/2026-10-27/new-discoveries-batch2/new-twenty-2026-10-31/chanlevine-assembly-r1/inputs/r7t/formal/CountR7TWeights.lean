import CountR7TStates
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace ChanLevine.Round7T
open Round6 Polynomial
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

def wordWeight (z : R) (g : ZMod n → R) (q : StateWord n) : R :=
  ∏ k, dominoMatrix z (g k) (q k) (q (k+1))

theorem inadmissible_weight (z : R) (g : ZMod n → R)
    (q : StateWord n) (hq : ¬ Admissible q) : wordWeight z g q = 0 := by
  have h : ∃ k, q k = 1 ∧ q (k+1) = 1 := by
    unfold Admissible at hq
    push Not at hq
    obtain ⟨k,hk,hn⟩ := hq
    exact ⟨k,hk,by omega⟩
  obtain ⟨k,hk,hn⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [dominoMatrix,hk,hn]

theorem matching_factor (z : R) (g : ZMod n → R)
    (s : Finset (ZMod n)) (hs : Matching s) (k : ZMod n) :
    dominoMatrix z (g k) (matchingWord s k) (matchingWord s (k+1)) =
      (if k ∈ s then -z else 1) *
      (if k ∈ s ∪ rightEnds s then g k else 1) *
      (if k ∈ s ∪ rightEnds s then 1 else 1+z) := by
  have hd := Finset.disjoint_left.mp (matching_disjoint s hs)
  by_cases hk : k ∈ s
  · have hr : k ∉ rightEnds s := fun h => hd hk h
    simp [matchingWord, hk, hr, dominoMatrix]
  · by_cases hr : k ∈ rightEnds s <;>
      simp [matchingWord, hk, hr, dominoMatrix]

theorem matching_weight (z : R) (g : ZMod n → R)
    (s : Finset (ZMod n)) (hs : Matching s) :
    wordWeight z g (matchingWord s) =
      (-z)^s.card * (1+z)^(n-2*s.card) * ∏ k ∈ s ∪ rightEnds s, g k := by
  unfold wordWeight
  simp_rw [matching_factor z g s hs]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have ha : (∏ k : ZMod n, if k ∈ s then -z else (1:R)) = (-z)^s.card := by
    simp
  have hb : (∏ k : ZMod n, if k ∈ s ∪ rightEnds s then g k else 1) =
      ∏ k ∈ s ∪ rightEnds s, g k := by
    rw [← Finset.prod_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc : (∏ k : ZMod n, if k ∈ s ∪ rightEnds s then (1:R) else 1+z) =
      (1+z)^(n-2*s.card) := by
    have hf : (Finset.univ.filter (fun k : ZMod n => k ∉ s ∪ rightEnds s)) =
        Finset.univ \ (s ∪ rightEnds s) := by ext k; simp
    have he : (Finset.univ \ (s ∪ rightEnds s)).card = n-2*s.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, endpoints_card s hs,
        Finset.card_univ, ZMod.card]
    calc
      _ = ∏ k : ZMod n, if k ∉ s ∪ rightEnds s then 1+z else 1 := by
        apply Finset.prod_congr rfl
        intro k _
        split_ifs <;> simp_all
      _ = _ := by rw [← Finset.prod_filter, Finset.prod_const, hf, he]

  rw [ha,hb,hc]
  ring
end ChanLevine.Round7T
