import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_20 :
    (∀ p : Points 5, p ≠ 20 → maskSet 70588740 p = true → maskSet 119920967 p = true) ∧
    (∀ p, step PG5 4 (maskSet 119920967) p = maskSet 119920967 p) ∧
    maskSet 119920967 20 = false := by decide
end Percolation
