import Mathlib
import GridRanks

namespace GridMajorization

lemma sum_antitone_le_image (n N : ℕ) (hn : 0<n) (hN : 0<N)
    (L : ℕ → ℕ) (hinj : Set.InjOn L (Finset.Icc 1 n))
    (hupper : ∀ r∈Finset.Icc 1 n, L r≤N)
    (hrank : ∀ r∈Finset.Icc 1 n, L r*n≤r*N)
    (φ : ℝ → ℝ) (hφ : AntitoneOn φ (Set.Icc 0 1)) :
    (∑ r∈Finset.Icc 1 n, φ ((r:ℝ)/n)) ≤
      ∑ r∈(Finset.Icc 1 n).image L, φ ((r:ℝ)/N) := by
  classical
  rw [Finset.sum_image (by intro a ha b hb hab;exact hinj ha hb hab)]
  apply Finset.sum_le_sum
  intro r hr
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hmem1 : (L r:ℝ)/(N:ℝ)∈Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hNp).2
      exact_mod_cast hupper r hr
  have hmem2 : (r:ℝ)/(n:ℝ)∈Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hnp).2
      exact_mod_cast (Finset.mem_Icc.mp hr).2
  apply hφ hmem1 hmem2
  apply (div_le_div_iff₀ hNp hnp).2
  exact_mod_cast hrank r hr

/-- Abstract assembly of an antitone grid inequality from a rank partition. -/
lemma sum_antitone_of_partition (j l : ℕ) (hj : 0<j) (hl : 0<l)
    (L R : ℕ → ℕ)
    (hLinj : Set.InjOn L (Finset.Icc 1 j)) (hRinj : Set.InjOn R (Finset.Icc 1 l))
    (hdisj : Disjoint ((Finset.Icc 1 j).image L) ((Finset.Icc 1 l).image R))
    (hpart : (Finset.Icc 1 j).image L ∪ (Finset.Icc 1 l).image R=Finset.Icc 1 (j+l))
    (hLrank : ∀ r∈Finset.Icc 1 j, L r*j≤r*(j+l))
    (hRrank : ∀ r∈Finset.Icc 1 l, R r*l≤r*(j+l))
    (φ : ℝ → ℝ) (hφ : AntitoneOn φ (Set.Icc 0 1)) :
    (∑ r∈Finset.Icc 1 j, φ ((r:ℝ)/j))+
      (∑ r∈Finset.Icc 1 l, φ ((r:ℝ)/l)) ≤
      ∑ r∈Finset.Icc 1 (j+l), φ ((r:ℝ)/(j+l)) := by
  have hk : 0<j+l := by omega
  have hLu : ∀ r∈Finset.Icc 1 j, L r≤j+l := by
    intro r hr
    have hm : L r∈Finset.Icc 1 (j+l) := by
      rw [← hpart]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem L hr)
    exact (Finset.mem_Icc.mp hm).2
  have hRu : ∀ r∈Finset.Icc 1 l, R r≤j+l := by
    intro r hr
    have hm : R r∈Finset.Icc 1 (j+l) := by
      rw [← hpart]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem R hr)
    exact (Finset.mem_Icc.mp hm).2
  have hL := sum_antitone_le_image j (j+l) hj hk L hLinj hLu hLrank φ hφ
  have hR := sum_antitone_le_image l (j+l) hl hk R hRinj hRu hRrank φ hφ
  simp only [Nat.cast_add] at hL hR
  calc
    _ ≤ (∑ r∈(Finset.Icc 1 j).image L, φ ((r:ℝ)/(j+l)))+
        (∑ r∈(Finset.Icc 1 l).image R, φ ((r:ℝ)/(j+l))) := add_le_add hL hR
    _ = ∑ r∈(Finset.Icc 1 j).image L ∪ (Finset.Icc 1 l).image R,
        φ ((r:ℝ)/(j+l)) := (Finset.sum_union hdisj).symm
    _ = _ := by rw [hpart]

/-- The merged rational grids dominate the separate grids for every decreasing function. -/
theorem antitone_grid_sum (j l : ℕ) (hj : 0<j) (hl : 0<l)
    (φ : ℝ → ℝ) (hφ : AntitoneOn φ (Set.Icc 0 1)) :
    (∑ r∈Finset.Icc 1 j, φ ((r:ℝ)/j)) +
      (∑ r∈Finset.Icc 1 l, φ ((r:ℝ)/l)) ≤
      ∑ r∈Finset.Icc 1 (j+l), φ ((r:ℝ)/(j+l)) := by
  apply sum_antitone_of_partition j l hj hl (GridRanks.L j l) (GridRanks.R j l)
      (GridRanks.L_injective j l).injOn (GridRanks.R_injective j l).injOn
  · exact GridRanks.ranks_disjoint hj hl
  · exact GridRanks.ranks_union hj hl
  · intro r hr
    have h := GridRanks.L_rank_bound j l r
    nlinarith
  · intro s hs
    have h := GridRanks.R_rank_bound (l := l) hj (Finset.mem_Icc.mp hs).1
    nlinarith
  · exact hφ

end GridMajorization
