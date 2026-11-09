import VerifiedDet
namespace Nut8.NewCertificates0132
def C4224 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4224 : C4224.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4224 : ¬ (C4224.det = 0 ∧ ∀ i, C4224.adjugate i i ≠ 0) := by
  intro h
  have := certificate4224
  rw [h.1] at this
  norm_num at this
def C4225 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4225 : C4225.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4225 : ¬ (C4225.det = 0 ∧ ∀ i, C4225.adjugate i i ≠ 0) := by
  intro h
  have := certificate4225
  rw [h.1] at this
  norm_num at this
def C4226 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4226 : C4226.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4226 : ¬ (C4226.det = 0 ∧ ∀ i, C4226.adjugate i i ≠ 0) := by
  intro h
  have := certificate4226
  rw [h.1] at this
  norm_num at this
def C4227 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4227 : C4227.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4227 : ¬ (C4227.det = 0 ∧ ∀ i, C4227.adjugate i i ≠ 0) := by
  intro h
  have := certificate4227
  rw [h.1] at this
  norm_num at this
def C4228 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4228 : C4228.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4228 : ¬ (C4228.det = 0 ∧ ∀ i, C4228.adjugate i i ≠ 0) := by
  intro h
  have := certificate4228
  rw [h.1] at this
  norm_num at this
def C4229 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4229 : C4229.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4229 : ¬ (C4229.det = 0 ∧ ∀ i, C4229.adjugate i i ≠ 0) := by
  intro h
  have := certificate4229
  rw [h.1] at this
  norm_num at this
def C4230 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4230 : C4230.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4230 : ¬ (C4230.det = 0 ∧ ∀ i, C4230.adjugate i i ≠ 0) := by
  intro h
  have := certificate4230
  rw [h.1] at this
  norm_num at this
def C4231 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4231 : C4231.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4231 : ¬ (C4231.det = 0 ∧ ∀ i, C4231.adjugate i i ≠ 0) := by
  intro h
  have := certificate4231
  rw [h.1] at this
  norm_num at this
def C4232 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4232 : C4232.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4232 : ¬ (C4232.det = 0 ∧ ∀ i, C4232.adjugate i i ≠ 0) := by
  intro h
  have := certificate4232
  rw [h.1] at this
  norm_num at this
def C4233 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate4233 : C4233.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4233 : ¬ (C4233.det = 0 ∧ ∀ i, C4233.adjugate i i ≠ 0) := by
  intro h
  have := certificate4233
  rw [h.1] at this
  norm_num at this
def C4234 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4234 : C4234.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4234 : ¬ (C4234.det = 0 ∧ ∀ i, C4234.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4234
def C4235 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4235 : C4235.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4235 : ¬ (C4235.det = 0 ∧ ∀ i, C4235.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4235
def C4236 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4236 : C4236.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4236 : ¬ (C4236.det = 0 ∧ ∀ i, C4236.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4236
def C4237 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate4237 : C4237.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4237 : ¬ (C4237.det = 0 ∧ ∀ i, C4237.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4237
def C4238 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4238 : C4238.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4238 : ¬ (C4238.det = 0 ∧ ∀ i, C4238.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4238
def C4239 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4239 : C4239.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4239 : ¬ (C4239.det = 0 ∧ ∀ i, C4239.adjugate i i ≠ 0) := by
  intro h
  have := certificate4239
  rw [h.1] at this
  norm_num at this
def C4240 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4240 : C4240.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4240 : ¬ (C4240.det = 0 ∧ ∀ i, C4240.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4240
def C4241 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4241 : C4241.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4241 : ¬ (C4241.det = 0 ∧ ∀ i, C4241.adjugate i i ≠ 0) := by
  intro h
  have := certificate4241
  rw [h.1] at this
  norm_num at this
def C4242 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4242 : C4242.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4242 : ¬ (C4242.det = 0 ∧ ∀ i, C4242.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4242
def C4243 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4243 : C4243.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4243 : ¬ (C4243.det = 0 ∧ ∀ i, C4243.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4243
def C4244 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4244 : C4244.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4244 : ¬ (C4244.det = 0 ∧ ∀ i, C4244.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4244
def C4245 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4245 : C4245.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4245 : ¬ (C4245.det = 0 ∧ ∀ i, C4245.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4245
def C4246 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4246 : C4246.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4246 : ¬ (C4246.det = 0 ∧ ∀ i, C4246.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4246
def C4247 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4247 : C4247.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4247 : ¬ (C4247.det = 0 ∧ ∀ i, C4247.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4247
def C4248 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate4248 : C4248.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4248 : ¬ (C4248.det = 0 ∧ ∀ i, C4248.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4248
def C4249 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate4249 : C4249.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4249 : ¬ (C4249.det = 0 ∧ ∀ i, C4249.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4249
def C4250 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4250 : C4250.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4250 : ¬ (C4250.det = 0 ∧ ∀ i, C4250.adjugate i i ≠ 0) := by
  intro h
  have := certificate4250
  rw [h.1] at this
  norm_num at this
def C4251 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4251 : C4251.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4251 : ¬ (C4251.det = 0 ∧ ∀ i, C4251.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4251
def C4252 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate4252 : C4252.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4252 : ¬ (C4252.det = 0 ∧ ∀ i, C4252.adjugate i i ≠ 0) := by
  intro h
  have := certificate4252
  rw [h.1] at this
  norm_num at this
def C4253 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate4253 : C4253.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4253 : ¬ (C4253.det = 0 ∧ ∀ i, C4253.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4253
def C4254 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4254 : C4254.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4254 : ¬ (C4254.det = 0 ∧ ∀ i, C4254.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4254
def C4255 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 2, 0]
theorem certificate4255 : C4255.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4255 : ¬ (C4255.det = 0 ∧ ∀ i, C4255.adjugate i i ≠ 0) := by
  intro h
  have := certificate4255
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0132
