import MidpointNormalForm
import NonSubring
import Lean

set_option autoImplicit false
set_option warningAsError true

open Lean Elab Command in
elab "#midpoint_inventory" : command => do
  for (name, info) in (← getEnv).constants do
    let s := name.toString
    if s.startsWith "JacobiShifted.Midpoint." || s.startsWith "_private.Midpoint" then
      logInfo m!"MIDPOINT_DECL {s}"
      logInfo m!"MIDPOINT_SAFETY {s} {info.isUnsafe}"

#midpoint_inventory
