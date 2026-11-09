import VerifiedDet
namespace Nut8.HardCofactor
def C : Matrix (Fin 8) (Fin 8) ℤ := !![0, 0, 0, 1, 0, 1, 0, 1; 0, -1, 0, 0, 1, 0, 0, 1; 0, 0, -1, 0, 0, 1, 1, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 2, 0, 0, 0; 1, 0, 1, 0, 0, -1, 0, 0; 0, 0, 1, 1, 0, 0, -1, 0; 1, 1, 0, 1, 0, 0, 0, 0]
theorem certificate : C.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
end Nut8.HardCofactor
