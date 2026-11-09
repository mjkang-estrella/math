import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace SteinerReflection
noncomputable section
def d (s : ℝ) := 2*s^3-26*s^2+32*s+30
def L (s : ℝ) := 86*s^3-728*s^2+894*s+810
def P (s : ℝ) := 29*d s+(s+29)^3*L s
lemma root_exists : ∃ s : ℝ, 5 < s ∧ s < 8 ∧ P s = 0 := by
  have hc : Continuous P := by unfold P d L; fun_prop
  have h5 : P 5 < 0 := by norm_num [P,d,L]
  have h8 : 0 < P 8 := by norm_num [P,d,L]
  obtain ⟨s, hs, hr⟩ := intermediate_value_Ioo (by norm_num : (5:ℝ) ≤ 8)
    hc.continuousOn ⟨h5,h8⟩
  exact ⟨s,hs.1,hs.2,hr⟩
lemma d_negative (s : ℝ) (h5 : 5 ≤ s) (h8 : s ≤ 8) : d s < 0 := by
  have he : d s = 30-48*s+2*s*(s-5)*(s-8) := by unfold d; ring
  have hn : 2*s*(s-5)*(s-8) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  rw [he]; linarith
lemma cubic_identities (s : ℝ) :
    29*(s^3-(s+1)^2*(14*s/15-1)) = 29*d s/30 ∧
    28*(s^3-(s+1)^2*(14*s/15-1))+(s^3-s/15-1) = L s/30 := by
  constructor <;> simp only [d, L] <;> ring
/-- Algebraic compatibility, with no tensor contraction premise hidden in the conclusion. -/
theorem algebraic_witness : ∃ s lam : ℝ, 5 < s ∧ s < 8 ∧ lam < 0 ∧
    29*d s/30 = lam*(s+29)^3 ∧ L s/30 = lam*(-1)^3 := by
  obtain ⟨s,h5,h8,hr⟩ := root_exists
  have hp : 0 < (s+29)^3 := by positivity
  have hn := d_negative s h5.le h8.le
  refine ⟨s,29*d s/(30*(s+29)^3),h5,h8,div_neg_of_neg_of_pos (by linarith) (by positivity),?_,?_⟩
  · field_simp
  · have he : 29*d s+(s+29)^3*L s = 0 := hr
    field_simp
    nlinarith [he]
end
end SteinerReflection
