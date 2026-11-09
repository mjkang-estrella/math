import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_3 :
    (∀ p : Points 5, p ≠ 3 → maskSet 241579737 p = true → maskSet 2137437909 p = true) ∧
    (∀ p, step PG5 5 (maskSet 2137437909) p = maskSet 2137437909 p) ∧
    maskSet 2137437909 3 = false := by decide
end Percolation
