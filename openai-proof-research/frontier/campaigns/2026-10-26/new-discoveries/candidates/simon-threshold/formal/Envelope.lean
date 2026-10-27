import Perspective
noncomputable section
open Set Real
namespace SimonThreshold
lemma envelope_convex (γ : ℝ) {s : ℝ} (hs : 0 < s) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun a => envelope γ a s) := by
  have hp := ConvexOn.smul (inv_nonneg.mpr hs.le)
    (perspective_convex kernel_strictConvex.convexOn hs)
  have hl : ConvexOn ℝ (Ioi (0 : ℝ)) (fun a => a * (1 + (log γ - kernel s) / s)) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  convert hl.add hp using 1
  ext a
  simp only [Pi.add_apply, smul_eq_mul, envelope]
  ring
lemma criterion_exp_iff (γ α β : ℝ) : SourceCriterion γ α β ↔
    ∀ t : ℝ, 0 < t →
      exp (-t) + γ * (exp (-(β - α) * t) * (1 - exp (-α * t))) ≤ 1 := by
  have heq : ∀ t : ℝ, exp (-(β - α) * t) * (1 - exp (-α * t)) =
      exp (-(β - α) * t) - exp (-β * t) := by
    intro t
    rw [mul_sub, mul_one, ← exp_add]
    congr 2
    ring
  constructor
  · intro h t ht
    have hz : exp (-t) ∈ Ioo (0 : ℝ) 1 :=
      ⟨exp_pos _, exp_lt_one_iff.mpr (by linarith)⟩
    have hh := h (exp (-t)) hz
    rw [rpow_def_of_pos hz.1, rpow_def_of_pos hz.1, log_exp] at hh
    have h1 : (-t) * (β - α) = -(β - α) * t := by ring
    have h2 : (-t) * β = -β * t := by ring
    simpa only [heq, h1, h2] using hh
  · intro h z hz
    have ht : 0 < -log z := neg_pos.mpr (log_neg hz.1 hz.2)
    have hh := h (-log z) ht
    rw [heq, neg_neg, exp_log hz.1] at hh
    rw [rpow_def_of_pos hz.1, rpow_def_of_pos hz.1]
    have h1 : log z * (β - α) = -(β - α) * (-log z) := by ring
    have h2 : log z * β = -β * (-log z) := by ring
    rw [h1, h2]
    exact hh
lemma exp_constraint_iff {γ α β t : ℝ} (hγ : 0 < γ) (hα : 0 < α) (ht : 0 < t) :
    exp (-t) + γ * (exp (-(β - α) * t) * (1 - exp (-α * t))) ≤ 1 ↔
      α + (log γ + log (1 - exp (-α * t)) - log (1 - exp (-t))) / t ≤ β := by
  have ha : 0 < 1 - exp (-α * t) := by
    apply sub_pos.mpr
    rw [exp_lt_one_iff]
    nlinarith
  have hb : 0 < 1 - exp (-t) := by
    apply sub_pos.mpr
    rw [exp_lt_one_iff]
    linarith
  have hp : 0 < γ * (exp (-(β - α) * t) * (1 - exp (-α * t))) :=
    mul_pos hγ (mul_pos (exp_pos _) ha)
  rw [← le_sub_iff_add_le']
  rw [← log_le_log_iff hp hb, log_mul (ne_of_gt hγ) (ne_of_gt (mul_pos (exp_pos _) ha)),
    log_mul (ne_of_gt (exp_pos _)) (ne_of_gt ha), log_exp]
  constructor
  · intro h
    have hd : (log γ + log (1 - exp (-α * t)) - log (1 - exp (-t))) / t ≤ β - α :=
      (div_le_iff₀ ht).2 (by nlinarith)
    linarith
  · intro h
    have hd : (log γ + log (1 - exp (-α * t)) - log (1 - exp (-t))) / t ≤ β - α := by
      linarith
    have hh := (div_le_iff₀ ht).1 hd
    nlinarith
end SimonThreshold
