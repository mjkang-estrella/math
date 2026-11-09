import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_10 :
    (∀ p : Points 5, p ≠ 10 → maskSet 241579737 p = true → maskSet 796310237 p = true) ∧
    (∀ p, step PG5 5 (maskSet 796310237) p = maskSet 796310237 p) ∧
    maskSet 796310237 10 = false := by decide
end Percolation
