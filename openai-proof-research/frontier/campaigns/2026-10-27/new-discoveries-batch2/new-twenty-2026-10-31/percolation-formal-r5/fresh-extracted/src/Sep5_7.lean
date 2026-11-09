import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_7 :
    (∀ p : Points 5, p ≠ 7 → maskSet 241579737 p = true → maskSet 795326041 p = true) ∧
    (∀ p, step PG5 5 (maskSet 795326041) p = maskSet 795326041 p) ∧
    maskSet 795326041 7 = false := by decide
end Percolation
