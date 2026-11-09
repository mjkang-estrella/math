import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_2 :
    (∀ p : Points 5, p ≠ 2 → maskSet 70588740 p = true → maskSet 657791315 p = true) ∧
    (∀ p, step PG5 4 (maskSet 657791315) p = maskSet 657791315 p) ∧
    maskSet 657791315 2 = false := by decide
end Percolation
