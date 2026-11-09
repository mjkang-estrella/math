import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_25 :
    (∀ p : Points 5, p ≠ 25 → maskSet 241579737 p = true → maskSet 1030209241 p = true) ∧
    (∀ p, step PG5 5 (maskSet 1030209241) p = maskSet 1030209241 p) ∧
    maskSet 1030209241 25 = false := by decide
end Percolation
