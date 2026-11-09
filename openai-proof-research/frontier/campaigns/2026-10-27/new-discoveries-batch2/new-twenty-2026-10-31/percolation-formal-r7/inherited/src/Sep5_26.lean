import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_26 :
    (∀ p : Points 5, p ≠ 26 → maskSet 241579737 p = true → maskSet 979810013 p = true) ∧
    (∀ p, step PG5 5 (maskSet 979810013) p = maskSet 979810013 p) ∧
    maskSet 979810013 26 = false := by decide
end Percolation
