import TorusPMD
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if (`TorusPMD).isPrefixOf n then
      if ci.isUnsafe || ci.isPartial then throwError "bad safety {n}"
      if (Lean.Compiler.getImplementedBy? env n).isSome then throwError "implemented_by {n}"
      if (getExternAttrData? env n).isSome then throwError "extern {n}"
      if n.toString.contains "_unsafe_rec" then throwError "unsafe recursion {n}"
      logInfo m!"SAFE_LOCAL {n}"
#print axioms TorusPMD.refutes_conjecture_4_7
