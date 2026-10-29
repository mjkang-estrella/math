import R8_8_0EdgeB0
import R8_8_0EdgeB1
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R8_8_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem edge_check : ∀ m : Fin 64, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by
  intro m
  by_cases h1 : m.val < 32
  ·
    have hb : m.val-0 < 32 := by omega
    have he : m.val-0+0 = m.val := by omega
    have hp := edge_checkB0 ⟨m.val-0,hb⟩
    simpa only [he] using hp
  ·
    have hb : m.val-32 < 32 := by omega
    have he : m.val-32+32 = m.val := by omega
    have hp := edge_checkB1 ⟨m.val-32,hb⟩
    simpa only [he] using hp
end R8_8_0
