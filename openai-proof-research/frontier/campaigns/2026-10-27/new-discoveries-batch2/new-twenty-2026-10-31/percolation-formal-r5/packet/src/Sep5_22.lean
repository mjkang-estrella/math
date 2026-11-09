import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_22 :
    (∀ p : Points 5, p ≠ 22 → maskSet 241579737 p = true → maskSet 2133210841 p = true) ∧
    (∀ p, step PG5 5 (maskSet 2133210841) p = maskSet 2133210841 p) ∧
    maskSet 2133210841 22 = false := by decide
end Percolation
