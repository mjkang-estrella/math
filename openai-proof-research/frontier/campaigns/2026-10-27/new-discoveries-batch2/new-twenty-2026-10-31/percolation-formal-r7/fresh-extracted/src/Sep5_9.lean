import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_9 :
    (∀ p : Points 5, p ≠ 9 → maskSet 241579737 p = true → maskSet 526824669 p = true) ∧
    (∀ p, step PG5 5 (maskSet 526824669) p = maskSet 526824669 p) ∧
    maskSet 526824669 9 = false := by decide
end Percolation
