import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_6 :
    (∀ p : Points 5, p ≠ 6 → maskSet 70588740 p = true → maskSet 741726996 p = true) ∧
    (∀ p, step PG5 4 (maskSet 741726996) p = maskSet 741726996 p) ∧
    maskSet 741726996 6 = false := by decide
end Percolation
