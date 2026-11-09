import VerifiedDet
namespace Nut8.NewCertificates0263
def C8416 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8416 : C8416.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8416 : ¬ (C8416.det = 0 ∧ ∀ i, C8416.adjugate i i ≠ 0) := by
  intro h
  have := certificate8416
  rw [h.1] at this
  norm_num at this
def C8417 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8417 : C8417.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8417 : ¬ (C8417.det = 0 ∧ ∀ i, C8417.adjugate i i ≠ 0) := by
  intro h
  have := certificate8417
  rw [h.1] at this
  norm_num at this
def C8418 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8418 : C8418.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8418 : ¬ (C8418.det = 0 ∧ ∀ i, C8418.adjugate i i ≠ 0) := by
  intro h
  have := certificate8418
  rw [h.1] at this
  norm_num at this
def C8419 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8419 : C8419.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8419 : ¬ (C8419.det = 0 ∧ ∀ i, C8419.adjugate i i ≠ 0) := by
  intro h
  have := certificate8419
  rw [h.1] at this
  norm_num at this
def C8420 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8420 : C8420.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8420 : ¬ (C8420.det = 0 ∧ ∀ i, C8420.adjugate i i ≠ 0) := by
  intro h
  have := certificate8420
  rw [h.1] at this
  norm_num at this
def C8421 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8421 : C8421.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8421 : ¬ (C8421.det = 0 ∧ ∀ i, C8421.adjugate i i ≠ 0) := by
  intro h
  have := certificate8421
  rw [h.1] at this
  norm_num at this
def C8422 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8422 : C8422.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8422 : ¬ (C8422.det = 0 ∧ ∀ i, C8422.adjugate i i ≠ 0) := by
  intro h
  have := certificate8422
  rw [h.1] at this
  norm_num at this
def C8423 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8423 : C8423.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8423 : ¬ (C8423.det = 0 ∧ ∀ i, C8423.adjugate i i ≠ 0) := by
  intro h
  have := certificate8423
  rw [h.1] at this
  norm_num at this
def C8424 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate8424 : C8424.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8424 : ¬ (C8424.det = 0 ∧ ∀ i, C8424.adjugate i i ≠ 0) := by
  intro h
  have := certificate8424
  rw [h.1] at this
  norm_num at this
def C8425 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate8425 : C8425.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8425 : ¬ (C8425.det = 0 ∧ ∀ i, C8425.adjugate i i ≠ 0) := by
  intro h
  have := certificate8425
  rw [h.1] at this
  norm_num at this
def C8426 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate8426 : C8426.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8426 : ¬ (C8426.det = 0 ∧ ∀ i, C8426.adjugate i i ≠ 0) := by
  intro h
  have := certificate8426
  rw [h.1] at this
  norm_num at this
def C8427 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate8427 : C8427.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8427 : ¬ (C8427.det = 0 ∧ ∀ i, C8427.adjugate i i ≠ 0) := by
  intro h
  have := certificate8427
  rw [h.1] at this
  norm_num at this
def C8428 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate8428 : C8428.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8428 : ¬ (C8428.det = 0 ∧ ∀ i, C8428.adjugate i i ≠ 0) := by
  intro h
  have := certificate8428
  rw [h.1] at this
  norm_num at this
def C8429 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate8429 : C8429.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8429 : ¬ (C8429.det = 0 ∧ ∀ i, C8429.adjugate i i ≠ 0) := by
  intro h
  have := certificate8429
  rw [h.1] at this
  norm_num at this
def C8430 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate8430 : C8430.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8430 : ¬ (C8430.det = 0 ∧ ∀ i, C8430.adjugate i i ≠ 0) := by
  intro h
  have := certificate8430
  rw [h.1] at this
  norm_num at this
def C8431 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate8431 : C8431.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8431 : ¬ (C8431.det = 0 ∧ ∀ i, C8431.adjugate i i ≠ 0) := by
  intro h
  have := certificate8431
  rw [h.1] at this
  norm_num at this
def C8432 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate8432 : C8432.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8432 : ¬ (C8432.det = 0 ∧ ∀ i, C8432.adjugate i i ≠ 0) := by
  intro h
  have := certificate8432
  rw [h.1] at this
  norm_num at this
def C8433 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate8433 : C8433.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8433 : ¬ (C8433.det = 0 ∧ ∀ i, C8433.adjugate i i ≠ 0) := by
  intro h
  have := certificate8433
  rw [h.1] at this
  norm_num at this
def C8434 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate8434 : C8434.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8434 : ¬ (C8434.det = 0 ∧ ∀ i, C8434.adjugate i i ≠ 0) := by
  intro h
  have := certificate8434
  rw [h.1] at this
  norm_num at this
def C8435 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate8435 : C8435.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8435 : ¬ (C8435.det = 0 ∧ ∀ i, C8435.adjugate i i ≠ 0) := by
  intro h
  have := certificate8435
  rw [h.1] at this
  norm_num at this
def C8436 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8436 : C8436.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8436 : ¬ (C8436.det = 0 ∧ ∀ i, C8436.adjugate i i ≠ 0) := by
  intro h
  have := certificate8436
  rw [h.1] at this
  norm_num at this
def C8437 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8437 : C8437.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8437 : ¬ (C8437.det = 0 ∧ ∀ i, C8437.adjugate i i ≠ 0) := by
  intro h
  have := certificate8437
  rw [h.1] at this
  norm_num at this
def C8438 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8438 : C8438.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8438 : ¬ (C8438.det = 0 ∧ ∀ i, C8438.adjugate i i ≠ 0) := by
  intro h
  have := certificate8438
  rw [h.1] at this
  norm_num at this
def C8439 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8439 : C8439.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8439 : ¬ (C8439.det = 0 ∧ ∀ i, C8439.adjugate i i ≠ 0) := by
  intro h
  have := certificate8439
  rw [h.1] at this
  norm_num at this
def C8440 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8440 : C8440.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8440 : ¬ (C8440.det = 0 ∧ ∀ i, C8440.adjugate i i ≠ 0) := by
  intro h
  have := certificate8440
  rw [h.1] at this
  norm_num at this
def C8441 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8441 : C8441.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8441 : ¬ (C8441.det = 0 ∧ ∀ i, C8441.adjugate i i ≠ 0) := by
  intro h
  have := certificate8441
  rw [h.1] at this
  norm_num at this
def C8442 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8442 : C8442.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8442 : ¬ (C8442.det = 0 ∧ ∀ i, C8442.adjugate i i ≠ 0) := by
  intro h
  have := certificate8442
  rw [h.1] at this
  norm_num at this
def C8443 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8443 : C8443.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8443 : ¬ (C8443.det = 0 ∧ ∀ i, C8443.adjugate i i ≠ 0) := by
  intro h
  have := certificate8443
  rw [h.1] at this
  norm_num at this
def C8444 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8444 : C8444.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8444 : ¬ (C8444.det = 0 ∧ ∀ i, C8444.adjugate i i ≠ 0) := by
  intro h
  have := certificate8444
  rw [h.1] at this
  norm_num at this
def C8445 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8445 : C8445.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8445 : ¬ (C8445.det = 0 ∧ ∀ i, C8445.adjugate i i ≠ 0) := by
  intro h
  have := certificate8445
  rw [h.1] at this
  norm_num at this
def C8446 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8446 : C8446.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8446 : ¬ (C8446.det = 0 ∧ ∀ i, C8446.adjugate i i ≠ 0) := by
  intro h
  have := certificate8446
  rw [h.1] at this
  norm_num at this
def C8447 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8447 : C8447.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8447 : ¬ (C8447.det = 0 ∧ ∀ i, C8447.adjugate i i ≠ 0) := by
  intro h
  have := certificate8447
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0263
