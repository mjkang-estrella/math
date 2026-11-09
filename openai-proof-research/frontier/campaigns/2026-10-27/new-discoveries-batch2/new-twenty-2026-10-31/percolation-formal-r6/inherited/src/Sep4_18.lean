import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_18 :
    (∀ p : Points 5, p ≠ 18 → maskSet 70588740 p = true → maskSet 640801110 p = true) ∧
    (∀ p, step PG5 4 (maskSet 640801110) p = maskSet 640801110 p) ∧
    maskSet 640801110 18 = false := by decide
end Percolation
