import Signed
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if origin == `Cube || origin == `Signed then
        unless `MathDB364205 |>.isPrefixOf n do
          throwError "Declaration outside namespace inventory: {n} from {origin}"
        count := count + 1
        logInfo m!"ORIGIN {origin} {n}"
  unless count == 33 do throwError "Unexpected declaration count {count}"
