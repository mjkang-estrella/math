module
import all URMatchingBase
import all URMatchingFinite
import all URMatchingDeletion
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owners := #[`URMatchingBase, `URMatchingFinite, `URMatchingDeletion]
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let owner := env.header.moduleNames[idx.toNat]!
      if owners.contains owner then
        count := count + 1
        let axs ← collectAxioms n
        let body := ci.value? (allowOpaque := true)
        logInfo m!"OWN {owner} {n} unsafe={ci.isUnsafe} body={body.isSome} axioms={axs} typeDeps={ci.type.getUsedConstants} bodyDeps={body.map Expr.getUsedConstants}"
        for ax in axs do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Forbidden axiom {ax} in {n}"
        if ci.isUnsafe then throwError "Unsafe declaration {n}"
  logInfo m!"ACTUAL_OWN_DECLARATION_COUNT {count}"
