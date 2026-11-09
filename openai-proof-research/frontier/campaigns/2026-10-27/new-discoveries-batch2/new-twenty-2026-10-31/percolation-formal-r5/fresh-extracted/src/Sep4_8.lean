import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_8 :
    (∀ p : Points 5, p ≠ 8 → maskSet 70588740 p = true → maskSet 255138375 p = true) ∧
    (∀ p, step PG5 4 (maskSet 255138375) p = maskSet 255138375 p) ∧
    maskSet 255138375 8 = false := by decide
end Percolation
