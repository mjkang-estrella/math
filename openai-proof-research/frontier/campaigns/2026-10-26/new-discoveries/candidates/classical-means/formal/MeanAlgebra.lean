import Mathlib

open Real
namespace ClassicalMeanRange

noncomputable def arithmetic (x y : ℝ) : ℝ := (x + y) / 2
noncomputable def geometric (x y : ℝ) : ℝ := Real.sqrt (x * y)
noncomputable def harmonic (x y : ℝ) : ℝ := 2 * x * y / (x + y)
noncomputable def quadratic (x y : ℝ) : ℝ := Real.sqrt ((x ^ 2 + y ^ 2) / 2)

lemma means_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < arithmetic x y ∧ 0 < geometric x y ∧
      0 < harmonic x y ∧ 0 < quadratic x y := by
  unfold arithmetic geometric harmonic quadratic
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

lemma means_square_relations {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    arithmetic x y * harmonic x y = (geometric x y) ^ 2 ∧
      (quadratic x y) ^ 2 = 2 * (arithmetic x y) ^ 2 - (geometric x y) ^ 2 := by
  have hsum : x + y ≠ 0 := by positivity
  have hg : (geometric x y) ^ 2 = x * y := Real.sq_sqrt (by positivity)
  have hq : (quadratic x y) ^ 2 = (x ^ 2 + y ^ 2) / 2 := Real.sq_sqrt (by positivity)
  constructor
  · rw [hg]
    unfold arithmetic harmonic
    field_simp
  · rw [hq, hg]
    unfold arithmetic
    ring

lemma means_order {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    harmonic x y ≤ geometric x y ∧ geometric x y ≤ arithmetic x y ∧
      arithmetic x y ≤ quadratic x y := by
  have hp := means_pos hx hy
  have hr := means_square_relations hx hy
  have hg : (geometric x y) ^ 2 = x * y := Real.sq_sqrt (by positivity)
  have hga : geometric x y ≤ arithmetic x y := by
    have ha : 0 ≤ arithmetic x y := hp.1.le
    unfold arithmetic at *
    nlinarith [sq_nonneg (x - y)]
  refine ⟨?_, hga, ?_⟩
  · nlinarith [sq_nonneg (geometric x y), mul_nonneg hp.2.1.le (sub_nonneg.mpr hga)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hga) (add_nonneg hp.1.le hp.2.1.le)]

/-- The source's sum comparison, proved from the literal four means. -/
lemma means_sum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    arithmetic x y + geometric x y ≤ quadratic x y + harmonic x y := by
  have hp := means_pos hx hy
  have hr := means_square_relations hx hy
  have ho := means_order hx hy
  have hgq : geometric x y ≤ quadratic x y := ho.2.1.trans ho.2.2
  have hsum : quadratic x y + geometric x y ≤ 2 * arithmetic x y := by
    nlinarith [sq_nonneg (quadratic x y - geometric x y)]
  have hprod := mul_nonneg (sub_nonneg.mpr hgq) (sub_nonneg.mpr hsum)
  nlinarith

/-- The source's product comparison, proved from the literal four means. -/
lemma means_product {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    quadratic x y * harmonic x y ≤ arithmetic x y * geometric x y := by
  have hp := means_pos hx hy
  have hr := means_square_relations hx hy
  have hid : (arithmetic x y * geometric x y) ^ 2 -
      (quadratic x y * harmonic x y) ^ 2 =
      arithmetic x y * harmonic x y * (arithmetic x y - harmonic x y) ^ 2 := by
    calc
      _ = (arithmetic x y) ^ 2 * (geometric x y) ^ 2 -
          (quadratic x y) ^ 2 * (harmonic x y) ^ 2 := by ring
      _ = _ := by rw [hr.2, ← hr.1]; ring
  have hnonneg : 0 ≤ arithmetic x y * harmonic x y *
      (arithmetic x y - harmonic x y) ^ 2 := mul_nonneg (mul_nonneg hp.1.le hp.2.2.1.le) (sq_nonneg _)
  have hap : 0 < arithmetic x y * geometric x y := mul_pos hp.1 hp.2.1
  have hqp : 0 < quadratic x y * harmonic x y := mul_pos hp.2.2.2 hp.2.2.1
  nlinarith

noncomputable def pairLeft (c : ℝ) : ℝ := c + Real.sqrt (c ^ 2 - 1)
noncomputable def pairRight (c : ℝ) : ℝ := c - Real.sqrt (c ^ 2 - 1)

lemma normalized_pair {c : ℝ} (hc : 1 ≤ c) :
    0 < pairLeft c ∧ 0 < pairRight c ∧
      arithmetic (pairLeft c) (pairRight c) = c ∧
      geometric (pairLeft c) (pairRight c) = 1 ∧
      harmonic (pairLeft c) (pairRight c) = 1 / c ∧
      quadratic (pairLeft c) (pairRight c) = Real.sqrt (2 * c ^ 2 - 1) := by
  have hrad : 0 ≤ c ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (c ^ 2 - 1)
  have hslt : Real.sqrt (c ^ 2 - 1) < c := by nlinarith
  have hprod : pairLeft c * pairRight c = 1 := by
    unfold pairLeft pairRight
    nlinarith
  have hsum : pairLeft c + pairRight c = 2 * c := by
    unfold pairLeft pairRight
    ring
  refine ⟨by unfold pairLeft; linarith, by unfold pairRight; linarith, ?_, ?_, ?_, ?_⟩
  · unfold arithmetic
    rw [hsum]
    ring
  · unfold geometric
    rw [hprod, Real.sqrt_one]
  · unfold harmonic
    rw [mul_assoc, hprod, hsum]
    ring
  · unfold quadratic
    congr 1
    nlinarith [sq_nonneg (pairLeft c + pairRight c)]

end ClassicalMeanRange
