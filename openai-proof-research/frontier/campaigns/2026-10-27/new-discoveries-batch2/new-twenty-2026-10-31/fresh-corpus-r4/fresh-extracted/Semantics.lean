import Mathlib
set_option autoImplicit false
namespace SpectralSemantics
noncomputable def radius (a b c d : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, (z-a)*(z-d)-(b:ℂ)*c=0 ∧ ‖z‖=r}
noncomputable def plusRoot (a b c d : ℝ) : ℝ := (a+d+Real.sqrt ((a-d)^2+4*b*c))/2
noncomputable def minusRoot (a b c d : ℝ) : ℝ := (a+d-Real.sqrt ((a-d)^2+4*b*c))/2

theorem roots {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (z : ℂ) :
    (z-a)*(z-d)-(b:ℂ)*c=0 ↔
      z=(plusRoot a b c d : ℂ) ∨ z=(minusRoot a b c d : ℂ) := by
  have hd : 0 ≤ (a-d)^2+4*b*c := by positivity
  have hs := Real.sq_sqrt hd
  have hs' : (Real.sqrt ((a-d)^2+4*b*c) : ℂ)^2 =
      ((a:ℂ)-d)^2+4*b*c := by exact_mod_cast hs
  have hf : (z-a)*(z-d)-(b:ℂ)*c =
      (z-(plusRoot a b c d : ℂ))*(z-(minusRoot a b c d : ℂ)) := by
    unfold plusRoot minusRoot
    push_cast
    linear_combination hs'/4
  rw [hf, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem root_bounds {a b c d : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ plusRoot a b c d ∧ |minusRoot a b c d| ≤ plusRoot a b c d := by
  have hs := Real.sqrt_nonneg ((a-d)^2+4*b*c)
  unfold plusRoot minusRoot
  constructor
  · positivity
  · rw [abs_le]; constructor <;> linarith

theorem radius_formula {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    radius a b c d = plusRoot a b c d := by
  have hbounds := root_bounds ha hb hc hd
  have hmem : plusRoot a b c d ∈ {r : ℝ | ∃ z : ℂ,
      (z-a)*(z-d)-(b:ℂ)*c=0 ∧ ‖z‖=r} := by
    refine ⟨(plusRoot a b c d : ℂ), (roots hb hc _).mpr (Or.inl rfl), ?_⟩
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbounds.1]
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro r ⟨z,hz,rfl⟩
    rcases (roots hb hc z).mp hz with rfl | rfl
    · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbounds.1, le_refl]
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hbounds.2
  · apply le_csSup _ hmem
    refine ⟨plusRoot a b c d, ?_⟩
    rintro r ⟨z,hz,rfl⟩
    rcases (roots hb hc z).mp hz with rfl | rfl
    · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbounds.1, le_refl]
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hbounds.2

theorem det_bridge (a b c d : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      !![(a:ℂ), (b:ℂ); (c:ℂ), (d:ℂ)]) = (z-a)*(z-d)-(b:ℂ)*c := by
  simp [Matrix.det_fin_two]

#print axioms radius_formula
#print axioms det_bridge
end SpectralSemantics
