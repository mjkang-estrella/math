import CotBoundary
noncomputable section
open Set
namespace EulerTuran
lemma iteratedDeriv_comp_mul_ne_zero (f : ℂ → ℂ) (c : ℂ) (hc : c ≠ 0)
    (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun z => f (c*z)) x = c^n * iteratedDeriv n f (c*x) := by
  let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (Units.mk0 c hc)
  have h := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) n
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hh := congrArg (fun T : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ =>
    T (fun _ => 1)) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at hh
  simp only [ContinuousLinearEquiv.coe_coe, g, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
    Units.val_mk0, smul_eq_mul, mul_one, Function.comp_def] at hh
  change iteratedDeriv n (fun z => f (c*z)) x =
    (iteratedFDeriv ℂ n f (c*x)) (fun _ => c) at hh
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hh
  simpa only [Finset.prod_const, Finset.card_fin, smul_eq_mul] using hh
lemma iteratedDeriv_affine (f : ℂ → ℂ) (a c : ℂ) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun z => f (a+c*z)) x = c^n * iteratedDeriv n f (a+c*x) := by
  have h := iteratedDeriv_comp_mul_ne_zero (fun z => f (a+z)) c hc n x
  simpa only [iteratedDeriv_comp_const_add] using h
end EulerTuran
