import ControlBase
import Sep5_0
import Sep5_3
import Sep5_4
import Sep5_6
import Sep5_7
import Sep5_9
import Sep5_10
import Sep5_12
import Sep5_13
import Sep5_17
import Sep5_18
import Sep5_21
import Sep5_22
import Sep5_25
import Sep5_26
import Sep5_27
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
def witness5 : Infection 5 := maskSet 241579737
def separators5 : List Nat := [510113500, 0, 0, 2137437909, 795293389, 0, 2120693407, 795326041, 0, 526824669, 796310237, 0, 2121246425, 526849757, 0, 0, 0, 526759641, 778286813, 0, 0, 256358109, 2133210841, 0, 0, 1030209241, 979810013, 929511165, 0, 0, 0]
def separator5 (v : Points 5) : Infection 5 := maskSet (separators5[v.val]!)
theorem full5 : Full (rounds PG5 5 witness5 3) := by unfold Full; decide
theorem early5 : ∀ k : Fin 3, ¬ Full (rounds PG5 5 witness5 k.val) := by unfold Full; decide
theorem time5 : TimeIs PG5 5 witness5 3 :=
  ⟨full5, fun k hk => early5 ⟨k,hk⟩⟩
theorem minimal5 : Minimal PG5 5 witness5 := by
  apply minimal_from_separators PG5 5 witness5 ⟨3, full5⟩
  intro v hv
  refine ⟨separator5 v, ?_⟩
  have casesV : v = 0 ∨ v = 3 ∨ v = 4 ∨ v = 6 ∨ v = 7 ∨ v = 9 ∨ v = 10 ∨ v = 12 ∨ v = 13 ∨ v = 17 ∨ v = 18 ∨ v = 21 ∨ v = 22 ∨ v = 25 ∨ v = 26 ∨ v = 27 := by
    revert hv
    revert v
    decide
  rcases casesV with h0 | h3 | h4 | h6 | h7 | h9 | h10 | h12 | h13 | h17 | h18 | h21 | h22 | h25 | h26 | h27
  · subst v
    exact ⟨sep5_0.1, funext sep5_0.2.1, sep5_0.2.2⟩
  · subst v
    exact ⟨sep5_3.1, funext sep5_3.2.1, sep5_3.2.2⟩
  · subst v
    exact ⟨sep5_4.1, funext sep5_4.2.1, sep5_4.2.2⟩
  · subst v
    exact ⟨sep5_6.1, funext sep5_6.2.1, sep5_6.2.2⟩
  · subst v
    exact ⟨sep5_7.1, funext sep5_7.2.1, sep5_7.2.2⟩
  · subst v
    exact ⟨sep5_9.1, funext sep5_9.2.1, sep5_9.2.2⟩
  · subst v
    exact ⟨sep5_10.1, funext sep5_10.2.1, sep5_10.2.2⟩
  · subst v
    exact ⟨sep5_12.1, funext sep5_12.2.1, sep5_12.2.2⟩
  · subst v
    exact ⟨sep5_13.1, funext sep5_13.2.1, sep5_13.2.2⟩
  · subst v
    exact ⟨sep5_17.1, funext sep5_17.2.1, sep5_17.2.2⟩
  · subst v
    exact ⟨sep5_18.1, funext sep5_18.2.1, sep5_18.2.2⟩
  · subst v
    exact ⟨sep5_21.1, funext sep5_21.2.1, sep5_21.2.2⟩
  · subst v
    exact ⟨sep5_22.1, funext sep5_22.2.1, sep5_22.2.2⟩
  · subst v
    exact ⟨sep5_25.1, funext sep5_25.2.1, sep5_25.2.2⟩
  · subst v
    exact ⟨sep5_26.1, funext sep5_26.2.1, sep5_26.2.2⟩
  · subst v
    exact ⟨sep5_27.1, funext sep5_27.2.1, sep5_27.2.2⟩
theorem control5 : ∃ a, Minimal PG5 5 a ∧ TimeIs PG5 5 a 3 := ⟨witness5, minimal5, time5⟩
end Percolation
