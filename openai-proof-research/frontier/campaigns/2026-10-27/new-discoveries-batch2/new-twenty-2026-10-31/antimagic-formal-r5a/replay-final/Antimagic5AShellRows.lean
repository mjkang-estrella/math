import Antimagic4AShell
namespace Antimagic.Round5A
open Finset

theorem offset_top (t n h : ℕ) (hh : n ≤ h + 1) : offset t n h = 0 := by
  apply sum_eq_zero
  intro g hg
  have := mem_range.mp hg
  simp [show ¬ h < g by omega]

theorem offset_step (t n h : ℕ) (hh : h + 1 < n) :
    offset t n h = t ^ (h + 1) + offset t n (h + 1) := by
  unfold offset
  have he : (∑ g ∈ range n, if h < g then t ^ g else 0) =
      (∑ g ∈ range n, if g = h + 1 then t ^ g else 0) +
      (∑ g ∈ range n, if h + 1 < g then t ^ g else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro g _
    by_cases h1 : g = h + 1
    · subst g; simp
    · by_cases h2 : h + 1 < g <;> simp [h1, h2, show (h < g) ↔ (h + 1 < g) by omega]
  rw [he]
  simp [hh]

theorem internalEdges_split (t n : ℕ) (hn : 1 < n) :
    internalEdges t n = t + offset t n 1 := by
  unfold internalEdges offset
  have he : (∑ g ∈ range n, if 1 ≤ g then t ^ g else 0) =
      (∑ g ∈ range n, if g = 1 then t ^ g else 0) +
      (∑ g ∈ range n, if 1 < g then t ^ g else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro g _
    by_cases h1 : g = 1
    · subst g; simp
    · by_cases h2 : 1 < g <;> simp [h1, h2, show (1 ≤ g) ↔ (1 < g) by omega]
  rw [he]
  simp [hn]

theorem offset_mono (t n : ℕ) {h g : ℕ} (hh : h ≤ g) :
    offset t n g ≤ offset t n h := by
  apply sum_le_sum
  intro i _
  by_cases hi : g < i
  · simp [hi, show h < i by omega]
  · simp [hi]

theorem offset_even (t n h : ℕ) (he : Even t) (hh : 1 ≤ h) : Even (offset t n h) := by
  apply even_iff_two_dvd.mpr
  apply Finset.dvd_sum
  intro g _
  split_ifs with hg
  · exact (even_iff_two_dvd.mp he).trans (dvd_pow_self t (by omega : g ≠ 0))
  · exact dvd_zero 2

theorem shell_size (t n : ℕ) (he : Even t) (hn : 3 ≤ n) :
    internalEdges t n - t = 2 * (center t n - 1) := by
  have hs := internalEdges_split t n (by omega)
  have hv := offset_even t n 1 he (by omega)
  obtain ⟨a,ha⟩ := hv
  simp only [center]
  omega

/-- Actual shell coordinates of distinct rows lie in disjoint intervals. -/
theorem shell_coordinate_injective (t n h g i j : ℕ)
    (hh : 2 ≤ h) (hg : 2 ≤ g) (hhn : h < n) (hgn : g < n)
    (hi : i < t ^ h) (hj : j < t ^ g)
    (eq : offset t n h + i = offset t n g + j) : h = g ∧ i = j := by
  have hsep : ∀ a b, 2 ≤ a → a < b → b < n → offset t n b + t ^ b ≤ offset t n a := by
    intro a b _ hab hbn
    have hs := offset_step t n (b - 1) (by omega)
    have hm := offset_mono t n (show a ≤ b - 1 by omega)
    rw [show b - 1 + 1 = b by omega] at hs
    omega
  have hge : h = g := by
    by_contra heq
    rcases lt_or_gt_of_ne heq with hl | hl
    · have := hsep h g hh hl hgn; omega
    · have := hsep g h hg hl hhn; omega
  subst g
  exact ⟨rfl, by omega⟩

/-- The shell row intervals cover their full range; this is symbolic in n. -/
theorem shell_coordinate_exists (t n h r : ℕ) (_hh : 1 ≤ h) (hr : r < offset t n h) :
    ∃ g i, h < g ∧ g < n ∧ i < t ^ g ∧ offset t n g + i = r := by
  induction n generalizing r with
  | zero => simp [offset] at hr
  | succ n ih =>
    by_cases hhn : h < n
    · have hs : offset t (n + 1) h = offset t n h + t ^ n := by
        simp [offset, sum_range_succ, hhn]
      by_cases hrn : r < t ^ n
      · exact ⟨n,r,hhn,by omega,hrn,by rw [offset_top t (n+1) n (by omega)]; omega⟩
      · obtain ⟨g,i,hg,hgn,hi,heq⟩ := ih (r - t ^ n) (by omega : r - t ^ n < offset t n h)
        refine ⟨g,i,hg,by omega,hi,?_⟩
        have hs' : offset t (n + 1) g = offset t n g + t ^ n := by
          simp [offset, sum_range_succ, hgn]
        rw [hs']; omega
    · rw [offset_top t (n+1) h (by omega)] at hr; omega

#print axioms shell_coordinate_injective
#print axioms shell_coordinate_exists
#print axioms shell_size
end Antimagic.Round5A
