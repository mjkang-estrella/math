import CDFLocal

/- Copyright 2026 Myeongjin Kang. MIT. Exact semantic instances and obstructions. -/
namespace CDFControls
open CDFLocal

theorem recentered_pair :
    ∃ d : Finset ℝ, d.card ≤ 1 ∧ (↑d : Set ℝ) ⊆ {-1, 1} ∧
      Covers ({-1, 1} : Set ℝ) d 2 := by
  have hc : Covers (id '' ({-1, 1} : Set ℝ)) ({0} : Finset ℝ) 1 := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨0, by simp, ?_⟩
    rcases hy with rfl | hy
    · norm_num [Real.dist_eq]
    · have hy' : y = 1 := hy
      subst y
      norm_num [Real.dist_eq]
  have hh := recenter_pullback id (K := 1) (by norm_num)
    (fun x y : ℝ => by simp) hc
  simpa using hh

theorem recenter_factor_one_false :
    ¬ ∃ z ∈ ({-1, 1} : Set ℝ), ∀ x ∈ ({-1, 1} : Set ℝ), dist x z ≤ 1 := by
  rintro ⟨z, hz, hcover⟩
  rcases hz with rfl | hz
  · have h := hcover 1 (by simp)
    norm_num [Real.dist_eq] at h
  · have hz' : z = 1 := hz
    subst z
    have h := hcover (-1) (by simp)
    norm_num [Real.dist_eq] at h

theorem strict_packing_pair : ({-1, 1} : Finset ℝ).card ≤ ({-1, 1} : Finset ℝ).card := by
  apply packing_bound (s := 1) (t := 0)
  · intro x hx y hy hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [Real.dist_eq] at *
  · intro x hx
    exact ⟨x, hx, by simp⟩
  · norm_num

theorem nonstrict_packing_obstruction :
    Covers ({-1, 1} : Set ℝ) ({0} : Finset ℝ) 1 ∧
    dist (-1 : ℝ) 1 = 2 ∧ ({0} : Finset ℝ).card < ({-1, 1} : Finset ℝ).card := by
  constructor
  · intro x hx
    refine ⟨0, by simp, ?_⟩
    rcases hx with rfl | hx
    · norm_num [Real.dist_eq]
    · have hx' : x = 1 := hx
      subst x
      norm_num [Real.dist_eq]
  · norm_num [Real.dist_eq]

theorem three_scales : ({0, 1, 2} : Finset ℕ).card ≤ 3 := by
  apply dyadic_window_card (L := 1/8) (U := 1)
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> norm_num [dyadic]
  · norm_num

theorem widened_window_obstruction :
    (1:ℝ) ≤ 2^(2+1)*(1/8) ∧ ({0, 1, 2} : Finset ℕ).card > 2 := by norm_num

theorem segment_instance :
    ∃ c : Finset ℝ, c.card ≤ 5 ∧ (↑c : Set ℝ) ⊆ segment ℝ 0 2 ∧
      Covers (segment ℝ (0:ℝ) 2) c (1/2) := by
  apply segment_cover
  norm_num [Real.dist_eq]

theorem segment_zero_instance :
    ∃ c : Finset ℝ, c.card ≤ 5 ∧ (↑c : Set ℝ) ⊆ segment ℝ 0 0 ∧
      Covers (segment ℝ (0:ℝ) 0) c 0 := by
  simpa using segment_cover (0:ℝ) 0 (r := 0) (by simp)

theorem cluster_constant_tight :
    dist (99/50:ℝ) (101/100) = (97/200)*2 ∧
    dist (99/50:ℝ) 2 ≤ 2/100 ∧ dist (101/100:ℝ) 1 ≤ 1/100 ∧
    dist (99/50:ℝ) (101/100) < (1/2)*2 := by norm_num [Real.dist_eq]

theorem fine_radius_obstruction :
    (1/32:ℝ)^2 ≤ (2*(1/64))^2+(2*(1/64))^2 ∧ ¬ (1/32:ℝ) < 1/64 := by norm_num

theorem low_count_tight : 65*(1:ℕ)^9+16*1^4 = 81*1^10 ∧
    ¬65*(1:ℕ)^9+16*1^4 ≤ 80*1^10 := by norm_num

end CDFControls
