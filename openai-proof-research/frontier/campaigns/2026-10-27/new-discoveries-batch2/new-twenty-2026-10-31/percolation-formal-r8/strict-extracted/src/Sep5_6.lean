import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_6 :
    (∀ p : Points 5, p ≠ 6 → maskSet 241579737 p = true → maskSet 2120693407 p = true) ∧
    (∀ p, step PG5 5 (maskSet 2120693407) p = maskSet 2120693407 p) ∧
    maskSet 2120693407 6 = false := by decide
end Percolation
