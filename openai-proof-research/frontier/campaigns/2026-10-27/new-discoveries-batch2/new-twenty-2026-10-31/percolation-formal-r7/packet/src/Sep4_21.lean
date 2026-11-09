import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_21 :
    (∀ p : Points 5, p ≠ 21 → maskSet 70588740 p = true → maskSet 756357973 p = true) ∧
    (∀ p, step PG5 4 (maskSet 756357973) p = maskSet 756357973 p) ∧
    maskSet 756357973 21 = false := by decide
end Percolation
