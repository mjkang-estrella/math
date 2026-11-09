import ControlBase
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
theorem sep4_26 :
    (∀ p : Points 5, p ≠ 26 → maskSet 70588740 p = true → maskSet 708123478 p = true) ∧
    (∀ p, step PG5 4 (maskSet 708123478) p = maskSet 708123478 p) ∧
    maskSet 708123478 26 = false := by decide
end Percolation
