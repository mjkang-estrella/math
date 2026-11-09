import Lean
open Lean
def probe : CoreM Unit := do
  let mut x := 0
  let xs : Array Nat := #[1,2]
  for n in xs do
    match () with
    | () =>
      let valO : Option Nat := some 3
      if valO.isSome then
        x := x + 1
  return
#eval 3
