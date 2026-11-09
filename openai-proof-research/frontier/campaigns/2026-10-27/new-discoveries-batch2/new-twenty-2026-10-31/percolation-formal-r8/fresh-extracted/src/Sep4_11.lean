import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_11 :
    (∀ p : Points 5, p ≠ 11 → maskSet 70588740 p = true → maskSet 624283989 p = true) ∧
    (∀ p, step PG5 4 (maskSet 624283989) p = maskSet 624283989 p) ∧
    maskSet 624283989 11 = false := by decide
end Percolation
