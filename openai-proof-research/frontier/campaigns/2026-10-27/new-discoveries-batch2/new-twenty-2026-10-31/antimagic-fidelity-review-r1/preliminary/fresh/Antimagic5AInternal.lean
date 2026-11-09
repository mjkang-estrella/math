import Antimagic5AShellRows
namespace Antimagic.Round5A
open Finset Round4A

theorem unpatched (t h i : ℕ) (ht : 4 ≤ t) : patchedIndex t h i = i := by
  simp [patchedIndex, show t ≠ 2 by omega]

theorem coordinate_bound (t n h i : ℕ) (hh : 2 ≤ h) (hn : h < n) (hi : i < t ^ h) :
    offset t n h + i < offset t n 1 := by
  have hs := offset_step t n (h - 1) (by omega)
  have hm := offset_mono t n (show 1 ≤ h - 1 by omega)
  rw [show h - 1 + 1 = h by omega] at hs
  omega

theorem internal_shell_range (t n h i : ℕ) (ht : 4 ≤ t) (he : Even t)
    (hh : 2 ≤ h) (hn : h < n) (hi : i < t ^ h) :
    1 ≤ internalLabel t n h i ∧
    internalLabel t n h i ≤ internalEdges t n - t + 1 ∧
    internalLabel t n h i ≠ center t n := by
  have hc := coordinate_bound t n h i hh hn hi
  have hs := internalEdges_split t n (by omega)
  have hz := shell_size t n he (by omega)
  have hZ : center t n - 1 < center t n := by simp [center]
  rw [internalLabel_shell t n h i (by omega), unpatched t h i ht]
  have hr := shellEntry_range (center t n) (center t n - 1) (offset t n h + i) hZ (by omega)
  omega

/-- Complete uniqueness across internal rows, including the root-edge row. -/
theorem internalLabel_injective (t n h g i j : ℕ) (ht : 4 ≤ t) (he : Even t)
    (hn3 : 3 ≤ n) (hh : 1 ≤ h) (hg : 1 ≤ g) (hhn : h < n) (hgn : g < n)
    (hi : i < t ^ h) (hj : j < t ^ g)
    (eq : internalLabel t n h i = internalLabel t n g j) : h = g ∧ i = j := by
  have hs := internalEdges_split t n (by omega)
  have hz := shell_size t n he (by omega)
  have hZ : 1 ≤ center t n := by simp [center]
  by_cases h1 : h = 1
  · subst h
    by_cases g1 : g = 1
    · subst g
      simp only [pow_one] at hi hj
      simp only [internalLabel, ite_true] at eq
      split_ifs at eq <;> omega
    · have hr := internal_shell_range t n g j ht he (by omega) hgn hj
      simp only [pow_one] at hi
      rw [show internalLabel t n 1 i = (if i = 0 then center t n else internalEdges t n - t + 1 + i) from rfl] at eq
      split_ifs at eq <;> omega
  · by_cases g1 : g = 1
    · subst g
      have hr := internal_shell_range t n h i ht he (by omega) hhn hi
      simp only [pow_one] at hj
      rw [show internalLabel t n 1 j = (if j = 0 then center t n else internalEdges t n - t + 1 + j) from rfl] at eq
      split_ifs at eq <;> omega
    · rw [internalLabel_shell t n h i h1, internalLabel_shell t n g j g1,
        unpatched t h i ht, unpatched t g j ht] at eq
      have hc := coordinate_bound t n h i (by omega) hhn hi
      have hd := coordinate_bound t n g j (by omega) hgn hj
      have hr : offset t n h + i < 2 * (center t n - 1) := by omega
      have hu : offset t n g + j < 2 * (center t n - 1) := by omega
      have hcEq := shellEntry_injective (center t n) (center t n - 1) (by omega)
        (a₁ := ⟨offset t n h + i, hr⟩) (a₂ := ⟨offset t n g + j, hu⟩) eq
      exact shell_coordinate_injective t n h g i j (by omega) (by omega) hhn hgn hi hj
        (congrArg Fin.val hcEq)

/-- Every internal label is attained in an actual row interval. -/
theorem internalLabel_exists (t n x : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n)
    (hx : 1 ≤ x ∧ x ≤ internalEdges t n) :
    ∃ h i, 1 ≤ h ∧ h < n ∧ i < t ^ h ∧ internalLabel t n h i = x := by
  have hs := internalEdges_split t n (by omega)
  have hz := shell_size t n he hn
  have hZ : 1 ≤ center t n := by simp [center]
  by_cases hxZ : x = center t n
  · exact ⟨1,0,by omega,by omega,by simpa using (show 0 < t by omega),by simp [internalLabel,hxZ]⟩
  by_cases hhigh : internalEdges t n - t + 1 < x
  · refine ⟨1,x - (internalEdges t n - t + 1),by omega,by omega,?_,?_⟩
    · simp only [pow_one]; omega
    · simp only [internalLabel, ite_true, show x - (internalEdges t n - t + 1) ≠ 0 by omega, ite_false]
      omega
  · obtain ⟨r,hr,_⟩ := shellEntry_unique (center t n) (center t n - 1) x (by omega) (by omega)
    obtain ⟨h,i,hh,hhn,hi,hri⟩ := shell_coordinate_exists t n 1 r.val (by omega) (by have := r.isLt; omega)
    refine ⟨h,i,by omega,hhn,hi,?_⟩
    rw [internalLabel_shell t n h i (by omega), unpatched t h i ht, hri]
    exact hr

#print axioms internalLabel_injective
#print axioms internalLabel_exists
end Antimagic.Round5A
