import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Tauto
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
namespace FloorCertificate
theorem node_478 (v466 : ℤ) : ((v466 = (0 : ℤ)) ↔ ((v466 ≤ (0 : ℤ)) ∧ (v466 ≥ (0 : ℤ)))) := by
  omega
theorem node_485 (v188 : ℤ) (v466 : ℤ) : ((v466 = v188) ↔ ((v466 ≤ v188) ∧ (v466 ≥ v188))) := by
  omega
theorem node_513 (v497 : ℤ) : ((v497 = (0 : ℤ)) ↔ ((v497 ≤ (0 : ℤ)) ∧ (v497 ≥ (0 : ℤ)))) := by
  omega
theorem node_519 (v497 : ℤ) (v507 : ℤ) : ((v497 = v507) ↔ ((v497 ≤ v507) ∧ (v497 ≥ v507))) := by
  omega
theorem node_737 (v17 : ℤ) : (((0 : ℤ) + v17) = v17) := by
  omega
theorem node_739 (v2 : ℤ) : (((1 : ℤ) * v2) = v2) := by
  omega
theorem node_744 (v2 : ℤ) (v17 : ℤ) : ((v17 - v2) = (v17 + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_763 (v2 : ℤ) : (((-(1 : ℤ)) * ((2 : ℤ) * v2)) = ((-(2 : ℤ)) * v2)) := by
  omega
theorem node_784 (v2 : ℤ) : (((-(1 : ℤ)) * ((3 : ℤ) * v2)) = ((-(3 : ℤ)) * v2)) := by
  omega
theorem node_805 (v2 : ℤ) : (((-(1 : ℤ)) * ((4 : ℤ) * v2)) = ((-(4 : ℤ)) * v2)) := by
  omega
theorem node_817 (v7 : ℤ) : ((v7) = v7) := by
  omega
theorem node_825 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) : (((v7 + v17) - v2) = ((v7 + v17) + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_829 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) : (((v7 + v17) + ((-(1 : ℤ)) * v2)) = (v7 + v17 + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_845 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) : (((v7 + v17) + ((-(2 : ℤ)) * v2)) = (v7 + v17 + ((-(2 : ℤ)) * v2))) := by
  omega
theorem node_862 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) : (((v7 + v17) + ((-(3 : ℤ)) * v2)) = (v7 + v17 + ((-(3 : ℤ)) * v2))) := by
  omega
theorem node_879 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) : (((v7 + v17) + ((-(4 : ℤ)) * v2)) = (v7 + v17 + ((-(4 : ℤ)) * v2))) := by
  omega
theorem node_888 (v110 : ℤ) : ((v110) = v110) := by
  omega
theorem node_896 (v2 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v110 + v17) - v2) = ((v110 + v17) + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_900 (v2 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v110 + v17) + ((-(1 : ℤ)) * v2)) = (v110 + v17 + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_916 (v2 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v110 + v17) + ((-(2 : ℤ)) * v2)) = (v110 + v17 + ((-(2 : ℤ)) * v2))) := by
  omega
theorem node_933 (v2 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v110 + v17) + ((-(3 : ℤ)) * v2)) = (v110 + v17 + ((-(3 : ℤ)) * v2))) := by
  omega
theorem node_950 (v2 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v110 + v17) + ((-(4 : ℤ)) * v2)) = (v110 + v17 + ((-(4 : ℤ)) * v2))) := by
  omega
theorem node_959 (v7 : ℤ) (v17 : ℤ) (v110 : ℤ) : ((v7 + v110 + v17) = (v7 + v110 + v17)) := by
  omega
theorem node_963 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v7 + v110 + v17) - v2) = ((v7 + v110 + v17) + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_966 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v7 + v110 + v17) + ((-(1 : ℤ)) * v2)) = (v7 + v110 + v17 + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_976 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v7 + v110 + v17) + ((-(2 : ℤ)) * v2)) = (v7 + v110 + v17 + ((-(2 : ℤ)) * v2))) := by
  omega
theorem node_986 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v7 + v110 + v17) + ((-(3 : ℤ)) * v2)) = (v7 + v110 + v17 + ((-(3 : ℤ)) * v2))) := by
  omega
theorem node_996 (v2 : ℤ) (v7 : ℤ) (v17 : ℤ) (v110 : ℤ) : (((v7 + v110 + v17) + ((-(4 : ℤ)) * v2)) = (v7 + v110 + v17 + ((-(4 : ℤ)) * v2))) := by
  omega
theorem node_1003 (v9 : ℤ) : ((v9) = v9) := by
  omega
theorem node_1011 (v2 : ℤ) (v9 : ℤ) (v17 : ℤ) : (((v9 + v17) - v2) = ((v9 + v17) + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_1015 (v2 : ℤ) (v9 : ℤ) (v17 : ℤ) : (((v9 + v17) + ((-(1 : ℤ)) * v2)) = (v9 + v17 + ((-(1 : ℤ)) * v2))) := by
  omega
theorem node_1031 (v2 : ℤ) (v9 : ℤ) (v17 : ℤ) : (((v9 + v17) + ((-(2 : ℤ)) * v2)) = (v9 + v17 + ((-(2 : ℤ)) * v2))) := by
  omega
theorem node_1048 (v2 : ℤ) (v9 : ℤ) (v17 : ℤ) : (((v9 + v17) + ((-(3 : ℤ)) * v2)) = (v9 + v17 + ((-(3 : ℤ)) * v2))) := by
  omega
theorem node_1065 (v2 : ℤ) (v9 : ℤ) (v17 : ℤ) : (((v9 + v17) + ((-(4 : ℤ)) * v2)) = (v9 + v17 + ((-(4 : ℤ)) * v2))) := by
  omega
theorem node_1074 (v7 : ℤ) (v9 : ℤ) (v17 : ℤ) : ((v7 + v9 + v17) = (v7 + v9 + v17)) := by
  omega
end FloorCertificate
