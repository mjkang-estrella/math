import PolynomialCertificates
import PointValues
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open Set
namespace BesselFejer

lemma normalizedDerivative_pos (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 9/4) :
    0 < normalizedDerivative q := by
  have hq : |q| ≤ 9 := by rw [abs_of_nonneg h0]; linarith
  have hp := h0_bound q (by simpa using h0) h1
  have he := (abs_le.mp (normalizedDerivative_error q hq)).1
  have hs : 2 * (9 : ℝ)^20 / (((20 : ℕ).factorial : ℝ) * ((21 : ℕ).factorial : ℝ)) <
      1/5 := by norm_num
  linarith

lemma besselJ0_negative_middle (x : ℝ) (h0 : 3 ≤ x) (h1 : x ≤ 55200/10000) :
    besselJ0 x < 0 := by
  have hx : 0 ≤ x := by linarith
  have hqa : 9/4 ≤ x^2/4 := by
    nlinarith [mul_nonneg (show 0 ≤ x-3 by linarith) hx]
  have hqb : x^2/4 ≤ (4761/625 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ (55200/10000 : ℝ)-x by linarith) hx]
  have hq : |x^2/4| ≤ 9 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hp := pNeg_bound (x^2/4) hqa hqb
  have he := (abs_le.mp (series_error (x^2/4) hq)).2
  have hs : 2*(9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2 < 1/50000 := by norm_num
  change series (x^2/4) < 0
  linarith

lemma normalizedDerivative_negative_second (x : ℝ)
    (h0 : 55200/10000 ≤ x) (h1 : x ≤ 55201/10000) :
    normalizedDerivative (x^2/4) < 0 := by
  have hx : 0 ≤ x := by linarith
  have hqa : (4761/625 : ℝ) ≤ x^2/4 := by
    nlinarith [mul_nonneg (show 0 ≤ x-(55200/10000 : ℝ) by linarith) hx]
  have hqb : x^2/4 ≤ (3047150401/400000000 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ (55201/10000 : ℝ)-x by linarith) hx]
  have hq : |x^2/4| ≤ 9 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hp := h2_bound (x^2/4) hqa hqb
  have he := (abs_le.mp (normalizedDerivative_error (x^2/4) hq)).2
  have hs : 2 * (9 : ℝ)^20 / (((20 : ℕ).factorial : ℝ) * ((21 : ℕ).factorial : ℝ)) <
      3/25 := by norm_num
  linarith

lemma besselJ0_strictAntiOn : StrictAntiOn besselJ0 (Icc (0 : ℝ) 3) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 3) besselJ0_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(besselJ0_hasDerivAt x).deriv]
  have hq0 : 0 ≤ x^2/4 := by positivity
  have hq1 : x^2/4 ≤ (9/4 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ 3-x by linarith [hx.2]) (le_of_lt hx.1)]
  exact mul_neg_of_neg_of_pos (by linarith [hx.1]) (normalizedDerivative_pos _ hq0 hq1)

lemma besselJ0_strictMonoOn_second :
    StrictMonoOn besselJ0 (Icc (55200/10000 : ℝ) (55201/10000)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) besselJ0_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(besselJ0_hasDerivAt x).deriv]
  apply mul_pos_of_neg_of_neg
  · linarith [hx.1]
  · exact normalizedDerivative_negative_second x (le_of_lt hx.1) (le_of_lt hx.2)

lemma exists_first_root : ∃ a : ℝ,
    a ∈ Icc (24048/10000 : ℝ) (24049/10000) ∧ besselJ0 a = 0 := by
  exact (intermediate_value_Icc' (by norm_num : (24048/10000 : ℝ) ≤ 24049/10000)
    besselJ0_continuous.continuousOn) ⟨le_of_lt rootAU_negative, le_of_lt rootAL_positive⟩

lemma exists_second_root : ∃ b : ℝ,
    b ∈ Icc (55200/10000 : ℝ) (55201/10000) ∧ besselJ0 b = 0 := by
  exact (intermediate_value_Icc (by norm_num : (55200/10000 : ℝ) ≤ 55201/10000)
    besselJ0_continuous.continuousOn) ⟨le_of_lt rootBL_negative, le_of_lt rootBU_positive⟩

lemma first_root_least (a : ℝ)
    (ha : a ∈ Icc (24048/10000 : ℝ) (24049/10000)) (hza : besselJ0 a = 0) :
    IsLeast {x : ℝ | 0 < x ∧ besselJ0 x = 0} a := by
  constructor
  · exact ⟨by linarith [ha.1], hza⟩
  · intro x hx
    by_contra h
    have hxa : x < a := lt_of_not_ge h
    have hh := besselJ0_strictAntiOn
      (show x ∈ Icc (0 : ℝ) 3 from ⟨le_of_lt hx.1, by linarith [ha.2]⟩)
      (show a ∈ Icc (0 : ℝ) 3 from ⟨by linarith [ha.1], by linarith [ha.2]⟩) hxa
    rw [hza, hx.2] at hh
    exact lt_irrefl _ hh

lemma second_root_least (a b : ℝ)
    (ha : a ∈ Icc (24048/10000 : ℝ) (24049/10000)) (hza : besselJ0 a = 0)
    (hb : b ∈ Icc (55200/10000 : ℝ) (55201/10000)) (hzb : besselJ0 b = 0) :
    IsLeast {x : ℝ | a < x ∧ besselJ0 x = 0} b := by
  constructor
  · exact ⟨by linarith [ha.2, hb.1], hzb⟩
  · intro x hx
    by_contra h
    have hxb : x < b := lt_of_not_ge h
    by_cases hx3 : x ≤ 3
    · have hh := besselJ0_strictAntiOn
        (show a ∈ Icc (0 : ℝ) 3 from ⟨by linarith [ha.1], by linarith [ha.2]⟩)
        (show x ∈ Icc (0 : ℝ) 3 from ⟨by linarith [ha.1, hx.1], hx3⟩) hx.1
      rw [hza, hx.2] at hh
      exact lt_irrefl _ hh
    · by_cases hxB : x ≤ 55200/10000
      · have hh := besselJ0_negative_middle x (le_of_not_ge hx3) hxB
        rw [hx.2] at hh
        exact lt_irrefl _ hh
      · have hh := besselJ0_strictMonoOn_second
          (show x ∈ Icc (55200/10000 : ℝ) (55201/10000) from
            ⟨le_of_not_ge hxB, by linarith [hb.2]⟩) hb hxb
        rw [hx.2, hzb] at hh
        exact lt_irrefl _ hh

lemma source_first_two_zero_bounds :
    sourceZero 1 ∈ Icc (24048/10000 : ℝ) (24049/10000) ∧
    sourceZero 2 ∈ Icc (55200/10000 : ℝ) (55201/10000) := by
  obtain ⟨a, ha, hza⟩ := exists_first_root
  obtain ⟨b, hb, hzb⟩ := exists_second_root
  have he1 : sourceZero 1 = a := by
    change nextZero 0 = a
    exact (first_root_least a ha hza).csInf_eq
  have he2 : sourceZero 2 = b := by
    change nextZero (sourceZero 1) = b
    rw [he1]
    exact (second_root_least a b ha hza hb hzb).csInf_eq
  exact ⟨he1.symm ▸ ha, he2.symm ▸ hb⟩

lemma source_first_two_characterization :
    IsLeast {x : ℝ | 0 < x ∧ besselJ0 x = 0} (sourceZero 1) ∧
    IsLeast {x : ℝ | sourceZero 1 < x ∧ besselJ0 x = 0} (sourceZero 2) := by
  obtain ⟨a, ha, hza⟩ := exists_first_root
  obtain ⟨b, hb, hzb⟩ := exists_second_root
  have hl1 := first_root_least a ha hza
  have he1 : sourceZero 1 = a := hl1.csInf_eq
  have hl2 := second_root_least a b ha hza hb hzb
  have he2 : sourceZero 2 = b := by
    change nextZero (sourceZero 1) = b
    rw [he1]
    exact hl2.csInf_eq
  rw [he1, he2]
  exact ⟨hl1, hl2⟩

end BesselFejer
