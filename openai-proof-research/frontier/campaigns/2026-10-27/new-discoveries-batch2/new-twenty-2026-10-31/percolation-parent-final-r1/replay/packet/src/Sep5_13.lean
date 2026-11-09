import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_13 :
    (∀ p : Points 5, p ≠ 13 → maskSet 241579737 p = true → maskSet 526849757 p = true) ∧
    (∀ p, step PG5 5 (maskSet 526849757) p = maskSet 526849757 p) ∧
    maskSet 526849757 13 = false := by decide
end Percolation
