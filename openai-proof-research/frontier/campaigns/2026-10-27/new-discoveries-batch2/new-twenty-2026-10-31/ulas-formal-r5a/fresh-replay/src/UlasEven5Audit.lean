import UlasEven5Final
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some path ← IO.getEnv "ULAS_AUDIT_OUT" | throwError "ULAS_AUDIT_OUT required"
  let shard := ((← IO.getEnv "ULAS_AUDIT_SHARD").getD "0").toNat!
  let handle ← IO.FS.Handle.mk path .write
  let mut count : Nat := 0
  let mut locals : Nat := 0
  for (n, ci) in env.constants.toList do
    if (hash n).toNat % 8 != shard then continue
    let mod := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
    let localDecl := mod.any (#[`UlasSeries, `UlasFinal, `UlasChecks, `UlasOperator, `UlasParity, `UlasLow, `UlasFinal2, `UlasWeight, `UlasFinal3, `UlasBridge, `UlasBinomial, `UlasReadout, `UlasPositive, `UlasExactReadout, `UlasInvariant, `UlasInitialization, `UlasFinal4, `UlasEven5Pell, `UlasEven5Coefficients, `UlasEven5Kummer, `UlasEven5Invariant, `UlasEven5Final].contains ·)
    let deps := ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).toArray.flatMap (·.getUsedConstants)
    let row := Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (mod.map Name.toString)),
      ("local", toJson localDecl), ("unsafe", toJson ci.isUnsafe),
      ("partial", toJson ci.isPartial), ("axiom", toJson ci.isAxiom),
      ("unsafe_rec", toJson (decide ((n.toString.splitOn "_unsafe_rec").length > 1))),
      ("implemented_by", toJson ((Compiler.getImplementedBy? env n).map Name.toString)),
      ("extern", toJson ((getExternAttrData? env n).isSome)),
      ("deps", toJson (deps.map Name.toString))]
    handle.putStrLn row.compress
    count := count + 1
    if localDecl then
      locals := locals + 1
      if ci.isUnsafe || ci.isPartial || ci.isAxiom || (Compiler.getImplementedBy? env n).isSome ||
          (getExternAttrData? env n).isSome then throwError "bad local metadata {n}"
      let axs ← collectAxioms n
      for ax in axs do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "bad local dependency {n}: {ax}"
      logInfo m!"LOCAL {n} AXIOMS {axs}"
  for idx in [:env.header.moduleData.size] do
    let md := env.header.moduleData[idx]!
    let mn := env.header.moduleNames[idx]!
    handle.putStrLn (Json.mkObj [
      ("module_record", toJson mn.toString),
      ("imports", toJson (md.imports.map (fun i => i.module.toString))),
      ("const_names", toJson (md.constNames.map Name.toString)),
      ("compiler_extra_names", toJson (md.extraConstNames.map Name.toString))]).compress
  handle.flush
  logInfo m!"AUDITED_SHARD {count} LOCAL {locals} ENV_TOTAL {env.constants.toList.length}"
  logInfo m!"IMPORT_MODULES {env.header.moduleNames}"
