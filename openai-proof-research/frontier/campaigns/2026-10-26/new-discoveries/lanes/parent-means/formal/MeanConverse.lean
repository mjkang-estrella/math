import MeanClassification

open Real
namespace ClassicalMeanRange

lemma exists_strict_source_positive {n : ℝ} (hn : 0 < n) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      (arithmetic x y)^n+(geometric x y)^n < (quadratic x y)^n+(harmonic x y)^n := by
  let e : ℝ := (5/4:ℝ)^n-1
  have he : 0 < e := by dsimp [e]; linarith [Real.one_lt_rpow (by norm_num : (1:ℝ)<5/4) hn]
  let c : ℝ := max 2 ((2/e)^(n⁻¹))
  have hc2 : 2 ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hcn : 2/e ≤ c^n := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0 ≤ (2/e:ℝ)) _)
      (le_max_right 2 ((2/e)^(n⁻¹))) hn.le
    simpa only [Real.rpow_inv_rpow (by positivity : 0 ≤ (2/e:ℝ)) hn.ne'] using h
  have hem : 2 ≤ e*c^n := (div_le_iff₀ he).mp hcn |>.trans_eq (mul_comm _ _)
  have hb : 0 ≤ 2*c^2-1 := by nlinarith
  have hq : (5/4:ℝ)*c ≤ Real.sqrt (2*c^2-1) := by
    have hs := Real.sq_sqrt hb
    have hp := Real.sqrt_nonneg (2*c^2-1)
    nlinarith [sq_nonneg (c-2)]
  have hqp := Real.rpow_le_rpow (by positivity : 0 ≤ (5/4:ℝ)*c) hq hn.le
  rw [Real.mul_rpow (by norm_num : 0 ≤ (5/4:ℝ)) hc0.le] at hqp
  have heq : (5/4:ℝ)^n=e+1 := by dsimp [e]; ring
  rw [heq] at hqp
  have hstrict : c^n+1 < (Real.sqrt (2*c^2-1))^n := by nlinarith
  rcases normalized_pair hc1 with ⟨hx,hy,ha,hg,hh,hqq⟩
  refine ⟨pairLeft c,pairRight c,hx,hy,?_⟩
  rw [ha,hg,hh,hqq,Real.one_rpow]
  have hpos : 0 < (1/c:ℝ)^n := Real.rpow_pos_of_pos (by positivity) _
  linarith

lemma exists_strict_source_negative {n : ℝ} (hn : n < 0) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      (arithmetic x y)^n+(geometric x y)^n < (quadratic x y)^n+(harmonic x y)^n := by
  let c : ℝ := max 2 ((3:ℝ)^((-n)⁻¹))
  have hc2 : 2 ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hneg : 0 < -n := by linarith
  have hcn : 3 ≤ c^(-n) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : 0 ≤ (3:ℝ)) _)
      (le_max_right 2 ((3:ℝ)^((-n)⁻¹))) hneg.le
    simpa only [Real.rpow_inv_rpow (by norm_num : 0 ≤ (3:ℝ)) hneg.ne'] using h
  have hsmall : c^n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 hn.le
  rcases normalized_pair hc1 with ⟨hx,hy,ha,hg,hh,hq⟩
  refine ⟨pairLeft c,pairRight c,hx,hy,?_⟩
  rw [ha,hg,hh,hq,Real.one_rpow]
  rw [one_div,Real.inv_rpow hc0.le,← Real.rpow_neg hc0.le]
  have hpos : 0 < (Real.sqrt (2*c^2-1))^n :=
    Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by nlinarith)) _
  linarith

def ConverseUniversallyValid (n : ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    (quadratic x y)^n+(harmonic x y)^n ≤ (arithmetic x y)^n+(geometric x y)^n

theorem source_converse_exponent_classification (n : ℝ) :
    ConverseUniversallyValid n ↔ n=0 := by
  constructor
  · intro h
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · obtain ⟨x,y,hx,hy,hs⟩ := exists_strict_source_negative hn
      exact (not_lt_of_ge (h x y hx hy)) hs
    · obtain ⟨x,y,hx,hy,hs⟩ := exists_strict_source_positive hn
      exact (not_lt_of_ge (h x y hx hy)) hs
  · rintro rfl x y _ _
    simp

/-- Complete universal exponent ranges for both directions of the source comparison. -/
theorem source_full_classification (n : ℝ) :
    (UniversallyValid n ↔ n ≤ 0 ∨ 1 ≤ n) ∧
      (ConverseUniversallyValid n ↔ n=0) :=
  ⟨source_exponent_classification n,source_converse_exponent_classification n⟩

end ClassicalMeanRange
