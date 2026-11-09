import PackedBits
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for i in [:env.header.moduleNames.size] do
    if #[`PackedRows, `PackedBits].contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        let ci := env.find? n |>.get!
        if ci.isPartial || ci.isUnsafe || ci.isAxiom then
          throwError "new forbidden helper {n}"
