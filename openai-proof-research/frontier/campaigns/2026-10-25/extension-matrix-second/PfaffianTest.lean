import Mathlib
namespace PfaffianTest
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def sourcePf (m : ℕ) (M : Matrix (Fin (2*m)) (Fin (2*m)) ℤ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin (2*m)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) *
    ∏ i : Fin m, M (σ ⟨2*i.val, by omega⟩) (σ ⟨2*i.val+1, by omega⟩)

def A0 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,0,0,0,0; -1,0,0,0,0,0; 0,0,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,2; 0,0,0,0,-2,0]
def A1 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,0,0,0,0; -1,0,-1,0,0,0; 0,1,0,1,0,0;
     0,0,-1,0,0,0; 0,0,0,0,0,2; 0,0,0,0,-2,0]

theorem same : sourcePf 3 A0 = sourcePf 3 A1 := by decide
end PfaffianTest
