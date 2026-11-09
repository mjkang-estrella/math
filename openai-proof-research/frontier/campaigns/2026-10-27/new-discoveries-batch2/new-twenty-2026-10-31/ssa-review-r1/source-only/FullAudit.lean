import SSA5.Audit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut flagged : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`SSA5).isPrefixOf env.header.moduleNames[idx.toNat]! then
        count := count + 1
        let axs ← liftCoreM (Lean.collectAxioms name)
        let body := ci.value? (allowOpaque := true)
        logInfo m!"DECL {name} TYPE {ci.type}
TYPE_HASH {ci.type.hash} BODY_HASH {body.map Expr.hash} REFERENCES {(ci.type.getUsedConstants ++ (body.map Expr.getUsedConstants).getD #[]).filter (fun n => (`SSA).isPrefixOf n)} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} AXIOMS {axs}"
        if ci.isUnsafe || ci.isPartial then flagged := flagged.push name
        for a in axs do
          unless allowed.contains a do throwError "disallowed axiom {a} in {name}"
  logInfo m!"FULL AUDIT: {count} declarations; unsafe/partial flags {flagged}"
