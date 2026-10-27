import PermanentThree
import ScalarBounds

namespace PermanentalThree

noncomputable def scaled (A : Mat3) (r c : Fin 3 → ℝ) : Mat3 :=
  fun i j => r i * A i j * c j

noncomputable def scaleFactor (r c : Fin 3 → ℝ) : ℝ :=
  r 0 * (r 1)^2 * r 2 * c 0 * (c 1)^2 * c 2

theorem scaled_det (A : Mat3) (r c : Fin 3 → ℝ) :
    (scaled A r c).det = (r 0*r 1*r 2*c 0*c 1*c 2)*A.det := by
  simp only [Matrix.det_fin_three, scaled]
  ring

theorem scaled_tp {A : Mat3} (hA : StrictTP3 A) {r c : Fin 3 → ℝ}
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) : StrictTP3 (scaled A r c) := by
  refine ⟨fun i j => mul_pos (mul_pos (hr i) (hA.1 i j)) (hc j), ?_, ?_⟩
  · intro i j k l hij hkl
    have hri := hr i; have hrj := hr j; have hck := hc k; have hcl := hc l
    have hf : 0 < r i*r j*c k*c l := by positivity
    have hm := hA.2.1 i j k l hij hkl
    have he : scaled A r c i k * scaled A r c j l -
        scaled A r c i l * scaled A r c j k =
        (r i*r j*c k*c l)*(A i k*A j l - A i l*A j k) := by
      unfold scaled
      ring
    rw [he]
    exact mul_pos hf hm
  · rw [scaled_det]
    have hr0 := hr 0; have hr1 := hr 1; have hr2 := hr 2
    have hc0 := hc 0; have hc1 := hc 1; have hc2 := hc 2
    exact mul_pos (by positivity) hA.2.2

theorem scaled_numerator (A : Mat3) (r c : Fin 3 → ℝ) :
    numerator (scaled A r c) = scaleFactor r c * numerator A := by
  unfold numerator per2 scaled scaleFactor
  ring

theorem scaled_denominator (A : Mat3) (r c : Fin 3 → ℝ) :
    denominator (scaled A r c) = scaleFactor r c * denominator A := by
  unfold denominator per3 scaled scaleFactor
  ring

theorem scaled_ratio (A : Mat3) {r c : Fin 3 → ℝ}
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    ratio (scaled A r c) = ratio A := by
  have hr0 := hr 0; have hr1 := hr 1; have hr2 := hr 2
  have hc0 := hc 0; have hc1 := hc 1; have hc2 := hc 2
  have hs : scaleFactor r c ≠ 0 := ne_of_gt (by unfold scaleFactor; positivity)
  unfold ratio
  rw [scaled_numerator, scaled_denominator, mul_div_mul_left _ _ hs]

noncomputable def normalize (A : Mat3) : Mat3 :=
  scaled A (fun i => (A i 0)⁻¹) (fun j => A 0 0 / A 0 j)

theorem normalize_tp {A : Mat3} (hA : StrictTP3 A) : StrictTP3 (normalize A) := by
  apply scaled_tp hA
  · intro i; exact inv_pos.mpr (hA.1 i 0)
  · intro j; exact div_pos (hA.1 0 0) (hA.1 0 j)

theorem normalize_ratio {A : Mat3} (hA : StrictTP3 A) : ratio (normalize A) = ratio A := by
  apply scaled_ratio
  · intro i; exact inv_pos.mpr (hA.1 i 0)
  · intro j; exact div_pos (hA.1 0 0) (hA.1 0 j)

theorem normalize_first_row {A : Mat3} (hA : StrictTP3 A) (j : Fin 3) :
    normalize A 0 j = 1 := by
  unfold normalize scaled
  have h00 := ne_of_gt (hA.1 0 0)
  have h0j := ne_of_gt (hA.1 0 j)
  field_simp

theorem normalize_first_col {A : Mat3} (hA : StrictTP3 A) (i : Fin 3) :
    normalize A i 0 = 1 := by
  unfold normalize scaled
  have h00 := ne_of_gt (hA.1 0 0)
  have hi0 := ne_of_gt (hA.1 i 0)
  field_simp

noncomputable def normalizedMatrix (x y z w : ℝ) : Mat3 :=
  !![1,1,1; 1,x,y; 1,z,w]

theorem normalize_eq {A : Mat3} (hA : StrictTP3 A) :
    normalize A = normalizedMatrix (normalize A 1 1) (normalize A 1 2)
      (normalize A 2 1) (normalize A 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedMatrix, normalize_first_row hA, normalize_first_col hA]

theorem normalized_matrix_bounds {x y z w : ℝ}
    (h : StrictTP3 (normalizedMatrix x y z w)) :
    (2:ℝ)/3 < ratio (normalizedMatrix x y z w) ∧
      ratio (normalizedMatrix x y z w) < (9:ℝ)/8 := by
  have hx := h.2.1 0 1 0 1 (by decide) (by decide)
  have hy := h.2.1 0 1 1 2 (by decide) (by decide)
  have hz := h.2.1 1 2 0 1 (by decide) (by decide)
  norm_num [normalizedMatrix] at hx hy hz
  have hd : 0 < normalizedDet x y z w := by
    have := h.2.2
    simpa [normalizedMatrix, Matrix.det_fin_three, normalizedDet] using this
  have hb := normalized_strict_bounds (by linarith : 1 < x)
    (by linarith : x < y) (by linarith : x < z) hd
  have hn : numerator (normalizedMatrix x y z w) = normalizedNumerator x y z w := by
    simp [numerator, per2, normalizedMatrix, normalizedNumerator, add_comm]
  have hden : denominator (normalizedMatrix x y z w) = normalizedDenominator x y z w := by
    simp [denominator, per3, normalizedMatrix, normalizedDenominator]
    ring
  have hp := denominator_pos h
  rw [hden] at hp
  unfold ratio
  rw [hn, hden]
  constructor
  · rw [lt_div_iff₀ hp]
    linarith [hb.1]
  · rw [div_lt_iff₀ hp]
    linarith [hb.2]

theorem source_universal_strict_bounds {A : Mat3} (hA : StrictTP3 A) :
    (2:ℝ)/3 < ratio A ∧ ratio A < (9:ℝ)/8 := by
  have h := normalized_matrix_bounds (normalize_eq hA ▸ normalize_tp hA)
  rw [← normalize_eq hA, normalize_ratio hA] at h
  exact h

end PermanentalThree
