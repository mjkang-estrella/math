import Controls
import Lean.Util.CollectAxioms
open Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[`Dynamics, `Reduction, `SourceSemantics, `Cardinality, `Endpoint, `Controls]
  let mut actual : Array Name := #[]
  for m in env.header.moduleNames do
    if expected.contains m then actual := actual.push m
  unless actual.size == expected.size do throwError "Local import closure mismatch"
  for m in actual do logInfo m!"AUDIT_MODULE {m}"
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if expected.contains owner then
      count := count + 1
      let axs ← collectAxioms n
      let impl := Lean.Compiler.getImplementedBy? env n
      let ext := isExtern env n
      logInfo m!"DECL {n} MODULE {owner} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} IMPLEMENTED_BY {impl} EXTERN {ext} AXIOMS {axs}"
      if ci.isUnsafe || ci.isPartial || impl.isSome || ext || n.toString.endsWith "_unsafe_rec" then
        throwError "Forbidden property {n}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} at {n}"
  logInfo m!"TOTAL_LOCAL_DECLARATIONS {count}"
#print axioms ChanLevine.mathdb_338887_conditional_full
#print ChanLevine.mathdb_338887_conditional_full
