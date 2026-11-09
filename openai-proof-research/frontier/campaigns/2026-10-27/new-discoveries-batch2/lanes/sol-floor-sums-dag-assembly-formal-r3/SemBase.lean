import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
structure Vars where
  (m H t a b c d : ℤ)
end Assembly
