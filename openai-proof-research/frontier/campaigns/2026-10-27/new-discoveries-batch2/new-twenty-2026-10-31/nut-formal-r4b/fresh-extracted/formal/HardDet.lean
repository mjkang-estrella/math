import VerifiedDet
namespace Nut8.HardDet
def C : Matrix (Fin 8) (Fin 8) ℤ := !![1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1]
theorem certificate : C.det = -3 := by
  rw [← sparseDet_eq_det]
  decide +kernel
end Nut8.HardDet
