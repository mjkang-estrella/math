import Witness
import Lean
set_option pp.all true
set_option pp.maxSteps 10000000
set_option format.width 200
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, info) in env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString) do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.header.moduleNames[idx]!
      if mod == `Definitions || mod == `Witness then
        count := count + 1
        logInfo m!"INVENTORY|{n}|{mod}|{info.isUnsafe}"
        logInfo m!"TYPE|{n}|{info.type}"
  logInfo m!"TOTAL|{count}"
