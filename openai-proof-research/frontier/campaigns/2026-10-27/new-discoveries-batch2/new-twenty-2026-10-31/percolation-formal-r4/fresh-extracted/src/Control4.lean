import ControlBase
import Sep4_2
import Sep4_6
import Sep4_8
import Sep4_11
import Sep4_12
import Sep4_16
import Sep4_18
import Sep4_20
import Sep4_21
import Sep4_26
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
def witness4 : Infection 5 := maskSet 70588740
def separators4 : List Nat := [0, 0, 657791315, 0, 0, 0, 741726996, 0, 255138375, 0, 0, 624283989, 238406470, 0, 0, 0, 221567813, 0, 640801110, 0, 119920967, 756357973, 0, 0, 0, 0, 708123478, 0, 0, 0, 0]
def separator4 (v : Points 5) : Infection 5 := maskSet (separators4[v.val]!)
theorem full4 : Full (rounds PG5 4 witness4 2) := by unfold Full; decide
theorem early4 : ∀ k : Fin 2, ¬ Full (rounds PG5 4 witness4 k.val) := by unfold Full; decide
theorem time4 : TimeIs PG5 4 witness4 2 :=
  ⟨full4, fun k hk => early4 ⟨k,hk⟩⟩
theorem minimal4 : Minimal PG5 4 witness4 := by
  apply minimal_from_separators PG5 4 witness4 ⟨2, full4⟩
  intro v hv
  refine ⟨separator4 v, ?_⟩
  have casesV : v = 2 ∨ v = 6 ∨ v = 8 ∨ v = 11 ∨ v = 12 ∨ v = 16 ∨ v = 18 ∨ v = 20 ∨ v = 21 ∨ v = 26 := by
    revert hv
    revert v
    decide
  rcases casesV with h2 | h6 | h8 | h11 | h12 | h16 | h18 | h20 | h21 | h26
  · subst v
    exact ⟨sep4_2.1, funext sep4_2.2.1, sep4_2.2.2⟩
  · subst v
    exact ⟨sep4_6.1, funext sep4_6.2.1, sep4_6.2.2⟩
  · subst v
    exact ⟨sep4_8.1, funext sep4_8.2.1, sep4_8.2.2⟩
  · subst v
    exact ⟨sep4_11.1, funext sep4_11.2.1, sep4_11.2.2⟩
  · subst v
    exact ⟨sep4_12.1, funext sep4_12.2.1, sep4_12.2.2⟩
  · subst v
    exact ⟨sep4_16.1, funext sep4_16.2.1, sep4_16.2.2⟩
  · subst v
    exact ⟨sep4_18.1, funext sep4_18.2.1, sep4_18.2.2⟩
  · subst v
    exact ⟨sep4_20.1, funext sep4_20.2.1, sep4_20.2.2⟩
  · subst v
    exact ⟨sep4_21.1, funext sep4_21.2.1, sep4_21.2.2⟩
  · subst v
    exact ⟨sep4_26.1, funext sep4_26.2.1, sep4_26.2.2⟩
theorem control4 : ∃ a, Minimal PG5 4 a ∧ TimeIs PG5 4 a 2 := ⟨witness4, minimal4, time4⟩
end Percolation
