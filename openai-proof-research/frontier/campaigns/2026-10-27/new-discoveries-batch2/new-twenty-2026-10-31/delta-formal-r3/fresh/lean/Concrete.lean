import Move00
import Move01
import Move02
import Move03
import Move04
import Move05
import Move06
import Move07
import Move08
import Move09
import Move10
import Move11
import Move12
import Move13
namespace Concrete
open Literal
theorem original_doubled_cubic : DoubledCubic g0 := by unfold DoubledCubic; decide
theorem pure_path : Pure g0 g7 := by
  apply Pure.step move0
  apply Pure.step move1
  apply Pure.step move2
  apply Pure.step move3
  apply Pure.step move4
  apply Pure.step move5
  apply Pure.step move6
  exact Pure.refl _
theorem seven_move_witness : Equivalent g7 g14 := by
  apply Equivalent.step (Or.inr move7)
  apply Equivalent.step (Or.inl move8)
  apply Equivalent.step (Or.inr move9)
  apply Equivalent.step (Or.inr move10)
  apply Equivalent.step (Or.inl move11)
  apply Equivalent.step (Or.inl move12)
  apply Equivalent.step (Or.inl move13)
  exact Equivalent.refl _
theorem order_drop : g14.order < g7.order := by decide
theorem chosen_order : g7.order = 11 := rfl
theorem nonminimal : ¬ Minimal g7 := smaller_equivalent_not_minimal seven_move_witness order_drop
#print axioms pure_path
#print axioms seven_move_witness
#print axioms nonminimal
end Concrete
