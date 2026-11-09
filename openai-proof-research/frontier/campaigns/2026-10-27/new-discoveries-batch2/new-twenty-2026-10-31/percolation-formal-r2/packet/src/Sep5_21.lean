import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_21 :
    (∀ p : Points 5, p ≠ 21 → maskSet 241579737 p = true → maskSet 256358109 p = true) ∧
    (∀ p, step PG5 5 (maskSet 256358109) p = maskSet 256358109 p) ∧
    maskSet 256358109 21 = false := by decide
end Percolation
