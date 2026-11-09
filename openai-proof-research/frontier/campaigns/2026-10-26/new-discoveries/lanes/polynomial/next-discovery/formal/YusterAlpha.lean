import YusterArithmetic

namespace YusterCounterexample

lemma phi_exists : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x + x^48 = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x + x^48) (Set.Icc 0 1) := by fun_prop
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hcont
    (by norm_num : (1:ℝ) ∈ Set.Icc ((0:ℝ)+0^48) ((1:ℝ)+1^48))
  refine ⟨x, ?_, ?_, he⟩
  · by_contra hn
    have hx0 : x = 0 := by linarith [hx.1]
    norm_num [hx0] at he
  · by_contra hn
    have hx1 : x = 1 := by linarith [hx.2]
    norm_num [hx1] at he

lemma phi_unique {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hex : x + x^48 = 1) (hey : y + y^48 = 1) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have hp : x^48 ≤ y^48 := pow_le_pow_left₀ hx (le_of_lt h) 48
    linarith
  · exact h
  · have hp : y^48 ≤ x^48 := pow_le_pow_left₀ hy (le_of_lt h) 48
    linarith

noncomputable def sourcePhi48 : ℝ := Classical.choose phi_exists

lemma sourcePhi48_spec : 0 < sourcePhi48 ∧ sourcePhi48 < 1 ∧
    sourcePhi48 + sourcePhi48^48 = 1 := Classical.choose_spec phi_exists

noncomputable def sourcePsi48 : ℝ := 1 - sourcePhi48

lemma sourcePsi48_spec : sourcePsi48 ∈ Set.Icc (0:ℝ) 1 ∧
    (1-sourcePsi48)^48=sourcePsi48 := by
  rcases sourcePhi48_spec with ⟨h0,h1,he⟩
  dsimp [sourcePsi48]
  constructor
  · constructor <;> linarith
  · have hi : 1-(1-sourcePhi48)=sourcePhi48 := by ring
    rw [hi]
    linarith

lemma sourcePsi48_unique {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (he : (1-x)^48=x) : x=sourcePsi48 := by
  have hp : 1-x=sourcePhi48 := phi_unique (by linarith [hx.2])
    (le_of_lt sourcePhi48_spec.1) (by linarith) sourcePhi48_spec.2.2
  dsimp [sourcePsi48]
  linarith

noncomputable def sourceAlpha48 : ℝ := sourcePhi48^47

lemma sourceAlpha48_pos : 0 < sourceAlpha48 := pow_pos sourcePhi48_spec.1 47

lemma sourceAlpha48_equation : sourceAlpha48*(1+sourceAlpha48)^47=1 := by
  have h : sourcePhi48*(1+sourcePhi48^47)=1 := by
    have he := sourcePhi48_spec.2.2
    calc
      sourcePhi48*(1+sourcePhi48^47) = sourcePhi48+sourcePhi48^48 := by ring
      _ = 1 := he
  have hp := congrArg (fun x : ℝ => x^47) h
  simpa only [mul_pow, one_pow, sourceAlpha48] using hp

lemma alpha_interval {a : ℝ} (ha : 0 ≤ a) (he : a*(1+a)^47=1) :
    (alphaLower:ℝ) < a ∧ a < (alphaUpper:ℝ) := by
  have hl : (0:ℝ) ≤ (alphaLower:ℝ) := by norm_num [alphaLower]
  have hu : (0:ℝ) ≤ (alphaUpper:ℝ) := by norm_num [alphaUpper]
  have hlo : (alphaLower:ℝ)*(1+(alphaLower:ℝ))^47<1 := by exact_mod_cast alphaLower_check
  have hhi : (1:ℝ)<(alphaUpper:ℝ)*(1+(alphaUpper:ℝ))^47 := by exact_mod_cast alphaUpper_check
  constructor
  · by_contra hn
    have hal : a ≤ (alphaLower:ℝ) := le_of_not_gt hn
    have hp : (1+a)^47 ≤ (1+(alphaLower:ℝ))^47 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 47
    have hm := mul_le_mul hal hp (by positivity : (0:ℝ) ≤ (1+a)^47) hl
    linarith
  · by_contra hn
    have hau : (alphaUpper:ℝ) ≤ a := le_of_not_gt hn
    have hp : (1+(alphaUpper:ℝ))^47 ≤ (1+a)^47 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 47
    have hm := mul_le_mul hau hp (by positivity : (0:ℝ) ≤ (1+(alphaUpper:ℝ))^47) ha
    linarith

lemma sourceAlpha48_interval : (alphaLower:ℝ) < sourceAlpha48 ∧
    sourceAlpha48 < (alphaUpper:ℝ) :=
  alpha_interval (le_of_lt sourceAlpha48_pos) sourceAlpha48_equation

end YusterCounterexample
