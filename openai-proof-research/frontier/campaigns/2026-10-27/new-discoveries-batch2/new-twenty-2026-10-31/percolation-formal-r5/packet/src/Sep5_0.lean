import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_0 :
    (∀ p : Points 5, p ≠ 0 → maskSet 241579737 p = true → maskSet 510113500 p = true) ∧
    (∀ p, step PG5 5 (maskSet 510113500) p = maskSet 510113500 p) ∧
    maskSet 510113500 0 = false := by decide
end Percolation
