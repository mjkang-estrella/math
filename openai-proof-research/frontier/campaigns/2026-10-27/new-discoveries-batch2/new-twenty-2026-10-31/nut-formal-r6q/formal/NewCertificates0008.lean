import VerifiedDet
namespace Nut8.NewCertificates0008
def C256 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate256 : C256.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction256 : ¬ (C256.det = 0 ∧ ∀ i, C256.adjugate i i ≠ 0) := by
  intro h
  have := certificate256
  rw [h.1] at this
  norm_num at this
def C257 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate257 : C257.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction257 : ¬ (C257.det = 0 ∧ ∀ i, C257.adjugate i i ≠ 0) := by
  intro h
  have := certificate257
  rw [h.1] at this
  norm_num at this
def C258 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate258 : C258.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction258 : ¬ (C258.det = 0 ∧ ∀ i, C258.adjugate i i ≠ 0) := by
  intro h
  have := certificate258
  rw [h.1] at this
  norm_num at this
def C259 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate259 : C259.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction259 : ¬ (C259.det = 0 ∧ ∀ i, C259.adjugate i i ≠ 0) := by
  intro h
  have := certificate259
  rw [h.1] at this
  norm_num at this
def C260 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate260 : C260.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction260 : ¬ (C260.det = 0 ∧ ∀ i, C260.adjugate i i ≠ 0) := by
  intro h
  have := certificate260
  rw [h.1] at this
  norm_num at this
def C261 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate261 : C261.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction261 : ¬ (C261.det = 0 ∧ ∀ i, C261.adjugate i i ≠ 0) := by
  intro h
  have := certificate261
  rw [h.1] at this
  norm_num at this
def C262 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate262 : C262.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction262 : ¬ (C262.det = 0 ∧ ∀ i, C262.adjugate i i ≠ 0) := by
  intro h
  have := certificate262
  rw [h.1] at this
  norm_num at this
def C263 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate263 : C263.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction263 : ¬ (C263.det = 0 ∧ ∀ i, C263.adjugate i i ≠ 0) := by
  intro h
  have := certificate263
  rw [h.1] at this
  norm_num at this
def C264 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate264 : C264.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction264 : ¬ (C264.det = 0 ∧ ∀ i, C264.adjugate i i ≠ 0) := by
  intro h
  have := certificate264
  rw [h.1] at this
  norm_num at this
def C265 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate265 : C265.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction265 : ¬ (C265.det = 0 ∧ ∀ i, C265.adjugate i i ≠ 0) := by
  intro h
  have := certificate265
  rw [h.1] at this
  norm_num at this
def C266 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate266 : C266.det = (-88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction266 : ¬ (C266.det = 0 ∧ ∀ i, C266.adjugate i i ≠ 0) := by
  intro h
  have := certificate266
  rw [h.1] at this
  norm_num at this
def C267 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate267 : C267.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction267 : ¬ (C267.det = 0 ∧ ∀ i, C267.adjugate i i ≠ 0) := by
  intro h
  have := certificate267
  rw [h.1] at this
  norm_num at this
def C268 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate268 : C268.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction268 : ¬ (C268.det = 0 ∧ ∀ i, C268.adjugate i i ≠ 0) := by
  intro h
  have := certificate268
  rw [h.1] at this
  norm_num at this
def C269 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate269 : C269.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction269 : ¬ (C269.det = 0 ∧ ∀ i, C269.adjugate i i ≠ 0) := by
  intro h
  have := certificate269
  rw [h.1] at this
  norm_num at this
def C270 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate270 : C270.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction270 : ¬ (C270.det = 0 ∧ ∀ i, C270.adjugate i i ≠ 0) := by
  intro h
  have := certificate270
  rw [h.1] at this
  norm_num at this
def C271 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate271 : C271.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction271 : ¬ (C271.det = 0 ∧ ∀ i, C271.adjugate i i ≠ 0) := by
  intro h
  have := certificate271
  rw [h.1] at this
  norm_num at this
def C272 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate272 : C272.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction272 : ¬ (C272.det = 0 ∧ ∀ i, C272.adjugate i i ≠ 0) := by
  intro h
  have := certificate272
  rw [h.1] at this
  norm_num at this
def C273 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate273 : C273.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction273 : ¬ (C273.det = 0 ∧ ∀ i, C273.adjugate i i ≠ 0) := by
  intro h
  have := certificate273
  rw [h.1] at this
  norm_num at this
def C274 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate274 : C274.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction274 : ¬ (C274.det = 0 ∧ ∀ i, C274.adjugate i i ≠ 0) := by
  intro h
  have := certificate274
  rw [h.1] at this
  norm_num at this
def C275 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate275 : C275.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction275 : ¬ (C275.det = 0 ∧ ∀ i, C275.adjugate i i ≠ 0) := by
  intro h
  have := certificate275
  rw [h.1] at this
  norm_num at this
def C276 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate276 : C276.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction276 : ¬ (C276.det = 0 ∧ ∀ i, C276.adjugate i i ≠ 0) := by
  intro h
  have := certificate276
  rw [h.1] at this
  norm_num at this
def C277 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate277 : C277.det = (-88 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction277 : ¬ (C277.det = 0 ∧ ∀ i, C277.adjugate i i ≠ 0) := by
  intro h
  have := certificate277
  rw [h.1] at this
  norm_num at this
def C278 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate278 : C278.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction278 : ¬ (C278.det = 0 ∧ ∀ i, C278.adjugate i i ≠ 0) := by
  intro h
  have := certificate278
  rw [h.1] at this
  norm_num at this
def C279 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate279 : C279.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction279 : ¬ (C279.det = 0 ∧ ∀ i, C279.adjugate i i ≠ 0) := by
  intro h
  have := certificate279
  rw [h.1] at this
  norm_num at this
def C280 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate280 : C280.det = (-132 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction280 : ¬ (C280.det = 0 ∧ ∀ i, C280.adjugate i i ≠ 0) := by
  intro h
  have := certificate280
  rw [h.1] at this
  norm_num at this
def C281 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate281 : C281.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction281 : ¬ (C281.det = 0 ∧ ∀ i, C281.adjugate i i ≠ 0) := by
  intro h
  have := certificate281
  rw [h.1] at this
  norm_num at this
def C282 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate282 : C282.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction282 : ¬ (C282.det = 0 ∧ ∀ i, C282.adjugate i i ≠ 0) := by
  intro h
  have := certificate282
  rw [h.1] at this
  norm_num at this
def C283 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate283 : C283.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction283 : ¬ (C283.det = 0 ∧ ∀ i, C283.adjugate i i ≠ 0) := by
  intro h
  have := certificate283
  rw [h.1] at this
  norm_num at this
def C284 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate284 : C284.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction284 : ¬ (C284.det = 0 ∧ ∀ i, C284.adjugate i i ≠ 0) := by
  intro h
  have := certificate284
  rw [h.1] at this
  norm_num at this
def C285 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate285 : C285.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction285 : ¬ (C285.det = 0 ∧ ∀ i, C285.adjugate i i ≠ 0) := by
  intro h
  have := certificate285
  rw [h.1] at this
  norm_num at this
def C286 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate286 : C286.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction286 : ¬ (C286.det = 0 ∧ ∀ i, C286.adjugate i i ≠ 0) := by
  intro h
  have := certificate286
  rw [h.1] at this
  norm_num at this
def C287 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate287 : C287.det = (-132 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction287 : ¬ (C287.det = 0 ∧ ∀ i, C287.adjugate i i ≠ 0) := by
  intro h
  have := certificate287
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0008
