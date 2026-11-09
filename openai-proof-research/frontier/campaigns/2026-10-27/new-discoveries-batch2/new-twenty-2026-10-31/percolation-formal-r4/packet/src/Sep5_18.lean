import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_18 :
    (∀ p : Points 5, p ≠ 18 → maskSet 241579737 p = true → maskSet 778286813 p = true) ∧
    (∀ p, step PG5 5 (maskSet 778286813) p = maskSet 778286813 p) ∧
    maskSet 778286813 18 = false := by decide
end Percolation
