import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_12 :
    (∀ p : Points 5, p ≠ 12 → maskSet 70588740 p = true → maskSet 238406470 p = true) ∧
    (∀ p, step PG5 4 (maskSet 238406470) p = maskSet 238406470 p) ∧
    maskSet 238406470 12 = false := by decide
end Percolation
