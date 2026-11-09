import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_12 :
    (∀ p : Points 5, p ≠ 12 → maskSet 241579737 p = true → maskSet 2121246425 p = true) ∧
    (∀ p, step PG5 5 (maskSet 2121246425) p = maskSet 2121246425 p) ∧
    maskSet 2121246425 12 = false := by decide
end Percolation
