import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_16 :
    (∀ p : Points 5, p ≠ 16 → maskSet 70588740 p = true → maskSet 221567813 p = true) ∧
    (∀ p, step PG5 4 (maskSet 221567813) p = maskSet 221567813 p) ∧
    maskSet 221567813 16 = false := by decide
end Percolation
