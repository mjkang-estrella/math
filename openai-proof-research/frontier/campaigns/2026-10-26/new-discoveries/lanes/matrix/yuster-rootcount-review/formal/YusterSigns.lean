import YusterAlpha

namespace YusterCounterexample

lemma rational_rho_negative (x : ℚ) (hx : x ∈ samplePoints) : rhoEval 48 x < 0 := by
  have h := rhoCheck_ok
  simp only [rhoCheck, List.all_eq_true, decide_eq_true_eq] at h
  exact h x hx

lemma rational_endpoint_signs :
    alphaLower*rhoEval 48 (1/100)-sigmaEval 48 (1/100)<0 ∧
    0<alphaUpper*rhoEval 48 (1/10)-sigmaEval 48 (1/10) ∧
    alphaLower*rhoEval 48 (1/2)-sigmaEval 48 (1/2)<0 ∧
    0<alphaUpper*rhoEval 48 (3/5)-sigmaEval 48 (3/5) ∧
    alphaLower*rhoEval 48 (4/5)-sigmaEval 48 (4/5)<0 := by
  have h := signCheck_ok
  simp only [signCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

lemma real_negative_sign {a : ℝ} {x : ℚ}
    (ha : (alphaLower:ℝ) ≤ a) (hr : rhoEval 48 x < 0)
    (he : alphaLower*rhoEval 48 x-sigmaEval 48 x<0) :
    (sourceP 48 a).eval (x:ℝ) < 0 := by
  rw [sourceP_eval]
  have hr' : (rhoEval 48 x:ℝ)<0 := by exact_mod_cast hr
  have he' : (alphaLower:ℝ)*(rhoEval 48 x:ℝ)-(sigmaEval 48 x:ℝ)<0 := by
    exact_mod_cast he
  nlinarith

lemma real_positive_sign {a : ℝ} {x : ℚ}
    (ha : a ≤ (alphaUpper:ℝ)) (hr : rhoEval 48 x < 0)
    (he : 0<alphaUpper*rhoEval 48 x-sigmaEval 48 x) :
    0 < (sourceP 48 a).eval (x:ℝ) := by
  rw [sourceP_eval]
  have hr' : (rhoEval 48 x:ℝ)<0 := by exact_mod_cast hr
  have he' : (0:ℝ)<(alphaUpper:ℝ)*(rhoEval 48 x:ℝ)-(sigmaEval 48 x:ℝ) := by
    exact_mod_cast he
  nlinarith

lemma signs_of_interval (a : ℝ) (ha : (alphaLower:ℝ) ≤ a)
    (hb : a ≤ (alphaUpper:ℝ)) :
    (sourceP 48 a).eval (1/100) < 0 ∧
    0 < (sourceP 48 a).eval (1/10) ∧
    (sourceP 48 a).eval (1/2) < 0 ∧
    0 < (sourceP 48 a).eval (3/5) ∧
    (sourceP 48 a).eval (4/5) < 0 := by
  rcases rational_endpoint_signs with ⟨h1,h2,h3,h4,h5⟩
  have r1 := rational_rho_negative (1/100) (by simp [samplePoints])
  have r2 := rational_rho_negative (1/10) (by simp [samplePoints])
  have r3 := rational_rho_negative (1/2) (by simp [samplePoints])
  have r4 := rational_rho_negative (3/5) (by simp [samplePoints])
  have r5 := rational_rho_negative (4/5) (by simp [samplePoints])
  exact ⟨by simpa using real_negative_sign ha r1 h1,
    by simpa using real_positive_sign hb r2 h2,
    by simpa using real_negative_sign ha r3 h3,
    by simpa using real_positive_sign hb r4 h4,
    by simpa using real_negative_sign ha r5 h5⟩

/-- The five strict alternating signs of the literal source polynomial. -/
theorem sourceP_signs :
    (sourceP 48 sourceAlpha48).eval (1/100) < 0 ∧
    0 < (sourceP 48 sourceAlpha48).eval (1/10) ∧
    (sourceP 48 sourceAlpha48).eval (1/2) < 0 ∧
    0 < (sourceP 48 sourceAlpha48).eval (3/5) ∧
    (sourceP 48 sourceAlpha48).eval (4/5) < 0 :=
  signs_of_interval sourceAlpha48 (le_of_lt sourceAlpha48_interval.1)
    (le_of_lt sourceAlpha48_interval.2)

end YusterCounterexample
