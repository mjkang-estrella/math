import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_17 :
    (∀ p : Points 5, p ≠ 17 → maskSet 241579737 p = true → maskSet 526759641 p = true) ∧
    (∀ p, step PG5 5 (maskSet 526759641) p = maskSet 526759641 p) ∧
    maskSet 526759641 17 = false := by decide
end Percolation
