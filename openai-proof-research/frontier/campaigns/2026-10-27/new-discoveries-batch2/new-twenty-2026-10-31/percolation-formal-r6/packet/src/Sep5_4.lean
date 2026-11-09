import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_4 :
    (∀ p : Points 5, p ≠ 4 → maskSet 241579737 p = true → maskSet 795293389 p = true) ∧
    (∀ p, step PG5 5 (maskSet 795293389) p = maskSet 795293389 p) ∧
    maskSet 795293389 4 = false := by decide
end Percolation
