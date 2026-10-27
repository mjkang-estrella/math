import Mathlib

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarBieberbach

theorem continuous_exp_kernel_zero {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (h : X → ℂ) (hh : Continuous h) (he : ∀ x, Complex.exp (h x) = 1)
    (x0 : X) (h0 : h x0 = 0) : ∀ x, h x = 0 := by
  have hs : {x | h x = 0} = (fun x => (h x).im) ⁻¹' Set.Ioo (-Real.pi) Real.pi := by
    ext x
    constructor
    · intro hx
      change -Real.pi < (h x).im ∧ (h x).im < Real.pi
      rw [hx]
      simp only [Complex.zero_im]
      constructor <;> linarith [Real.pi_pos]
    · intro hx
      apply Complex.exp_inj_of_neg_pi_lt_of_le_pi hx.1 hx.2.le
      · simp only [Complex.zero_im]
        linarith [Real.pi_pos]
      · simp only [Complex.zero_im]
        exact Real.pi_pos.le
      · simpa only [Complex.exp_zero] using he x
  have hc : IsClosed {x | h x = 0} := isClosed_eq hh continuous_const
  have ho : IsOpen {x | h x = 0} := by
    rw [hs]
    exact isOpen_Ioo.preimage (Complex.continuous_im.comp hh)
  have hu : {x | h x = 0} = Set.univ := IsClopen.eq_univ ⟨hc, ho⟩ ⟨x0, h0⟩
  intro x
  change x ∈ {x | h x = 0}
  rw [hu]
  trivial

end CStarBieberbach
