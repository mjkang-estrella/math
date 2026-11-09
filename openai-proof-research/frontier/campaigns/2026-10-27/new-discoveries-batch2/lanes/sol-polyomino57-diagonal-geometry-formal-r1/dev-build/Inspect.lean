import Diagonal
open Polyomino57
example (p : GridPoint) : p ∈ square ↔ -5 ≤ p.1 ∧ p.1 ≤ 5 ∧ -5 ≤ p.2 ∧ p.2 ≤ 5 := by
  simp [square,List.mem_flatMap]
  trace_state
