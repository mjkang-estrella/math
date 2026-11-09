import OrdinalLine
set_option warningAsError true
namespace OrdinalSpaces366371
/-- The core linear contradiction once the six points are known to lie in increasing order. -/
theorem core_copy (a : Fin 6 → ℝ) (h05 : a 0 < a 5)
    (hlt : ∀ x y z w : Fin 6, D x y < D z w → |a x - a y| < |a z - a w|) : False := by
  have hd : ∀ {s t : ℝ}, s < t → |s - t| = t - s := fun h => by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
  have h05' : |a 0 - a 5| = a 5 - a 0 := hd h05
  -- every point lies strictly between `a 0` and `a 5`
  have key : ∀ x : Fin 6, x ≠ 0 → x ≠ 5 → D 0 x < D 0 5 ∧ D x 5 < D 0 5 := by decide
  have between : ∀ x : Fin 6, x ≠ 0 → x ≠ 5 → a 0 < a x ∧ a x < a 5 := by
    intro x hx0 hx5
    have h1 := hlt 0 x 0 5 (key x hx0 hx5).1
    have h2 := hlt x 5 0 5 (key x hx0 hx5).2
    rw [h05'] at h1 h2
    have := abs_lt.1 h2
    have := (abs_lt.1 h1)
    constructor <;> linarith
  obtain ⟨b1, c1⟩ := between 1 (by decide) (by decide)
  obtain ⟨b2, c2⟩ := between 2 (by decide) (by decide)
  obtain ⟨b3, c3⟩ := between 3 (by decide) (by decide)
  obtain ⟨b4, c4⟩ := between 4 (by decide) (by decide)
  -- the order is forced by the distances from point 0
  have o12 := hlt 0 1 0 2 (by decide)
  have o23 := hlt 0 2 0 3 (by decide)
  have o34 := hlt 0 3 0 4 (by decide)
  rw [hd b1, hd b2] at o12; rw [hd b2, hd b3] at o23; rw [hd b3, hd b4] at o34
  have e12 : a 1 < a 2 := by linarith
  have e23 : a 2 < a 3 := by linarith
  have e34 : a 3 < a 4 := by linarith
  -- the five comparisons whose sum is `0 < 0`
  have q1 := hlt 2 3 3 4 (by decide)
  have q2 := hlt 1 2 2 4 (by decide)
  have q3 := hlt 0 1 1 3 (by decide)
  have q4 := hlt 1 4 4 5 (by decide)
  have q5 := hlt 3 5 0 2 (by decide)
  rw [hd e23, hd e34] at q1
  rw [hd e12, hd (e23.trans e34)] at q2
  rw [hd b1, hd (e12.trans e23)] at q3
  rw [hd ((e12.trans e23).trans e34), hd c4] at q4
  rw [hd c3, hd b2] at q5
  linarith
end OrdinalSpaces366371
