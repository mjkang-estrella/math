import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep5_27 :
    (∀ p : Points 5, p ≠ 27 → maskSet 241579737 p = true → maskSet 929511165 p = true) ∧
    (∀ p, step PG5 5 (maskSet 929511165) p = maskSet 929511165 p) ∧
    maskSet 929511165 27 = false := by decide
end Percolation
