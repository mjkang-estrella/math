import VerifiedDet
namespace Nut8.Pilot
def C0 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
theorem certificate0 : (C0).det = 48 := by
  rw [← sparseDet_eq_det]
  decide +kernel
def C1 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 0, 0, 0, 0, 1, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, -2, 0, 0, 0, 1, 0; 0, 0, 0, -2, 0, 0, 0, 1; 0, 0, 0, 0, -2, 0, 0, 1; 1, 0, 0, 0, 0, 1, 0, 1; 1, 1, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate1 : (C1).adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
end Nut8.Pilot
