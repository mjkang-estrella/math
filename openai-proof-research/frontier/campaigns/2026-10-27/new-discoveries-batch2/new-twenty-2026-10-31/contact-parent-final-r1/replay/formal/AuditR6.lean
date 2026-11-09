import AuditR5
import RefutationLocal
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxRecDepth 8192
/- Lossless expression DAG output avoids expanding shared kernel proof terms
exponentially. NODE references are scoped to one declaration, shared by its
type and opaque-inclusive value. Every Expr constructor and payload is kept. -/
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "CONTACT_AUDIT_PATH").getD "AuditR6.dag"
  let handle ← IO.FS.Handle.mk path .write
  let stream := IO.FS.Stream.ofHandle handle
  let intern (e : Expr) : StateT (Std.HashMap Expr Nat × Array Expr) IO Nat := do
    let (seen, todo) ← get
    if let some i := seen[e]? then return i
    let i := seen.size
    set (seen.insert e i, todo.push e)
    return i
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if mod == `SourceContact || mod == `QuadraticBranches || mod == `ExactOrders ||
        mod == `SecondBranch || mod == `BranchBounds || mod == `HalfPlane ||
        mod == `GraphResolvent || mod == `Audit || mod == `AuditR2 ||
        mod == `Coprimality || mod == `CayleyPolynomials || mod == `BidiskReduced ||
        mod == `AuditR3 || mod == `BidiskStable || mod == `BidiskDegrees ||
        mod == `BidiskReflection || mod == `BidiskCertificate || mod == `AuditR4 ||
        mod == `RootLocalization || mod == `CayleyRootBridge || mod == `CayleyLocalization || mod == `CayleyHeight || mod == `ParameterizedContact || mod == `CircleChart || mod == `BidiskContact || mod == `ContactExclusion || mod == `Refutation || mod == `AuditR5 || mod == `SourceContactLocal || mod == `ContactUniqueness ||
        mod == `LocalBidiskContact || mod == `RefutationLocal || mod == `AuditR6 then
      count := count + 1
      let axs ← collectAxioms name
      liftIO <| stream.putStrLn s!"DECL {name}\nMODULE {mod}\nUNSAFE {ci.isUnsafe}\nPARTIAL {ci.isPartial}\nAXIOMS {axs}"
      let action : StateT (Std.HashMap Expr Nat × Array Expr) IO Unit := do
        let ti ← intern ci.type
        liftM <| stream.putStrLn s!"TYPE_REF {ti}"
        match ci.value? (allowOpaque := true) with
        | none => liftM <| stream.putStrLn "BODY_NONE"
        | some value =>
          let vi ← intern value
          liftM <| stream.putStrLn s!"BODY_REF {vi}"
        while !(← get).2.isEmpty do
          let (seen, todo) ← get
          let e := todo.back!
          set (seen, todo.pop)
          let id := seen[e]!
          let payload ← match e with
            | .bvar i => pure s!"bvar {i}"
            | .fvar i => pure s!"fvar {repr i}"
            | .mvar i => pure s!"mvar {repr i}"
            | .sort u => pure s!"sort {repr u}"
            | .const n us => pure s!"const {repr n} {repr us}"
            | .app f a => do
              let fi ← intern f
              let ai ← intern a
              pure s!"app {fi} {ai}"
            | .lam n t b bi => do
              let ti ← intern t
              let bi' ← intern b
              pure s!"lam {repr n} {ti} {bi'} {repr bi}"
            | .forallE n t b bi => do
              let ti ← intern t
              let bi' ← intern b
              pure s!"forallE {repr n} {ti} {bi'} {repr bi}"
            | .letE n t v b nd => do
              let ti ← intern t
              let vi ← intern v
              let bi ← intern b
              pure s!"letE {repr n} {ti} {vi} {bi} {nd}"
            | .lit l => pure s!"lit {repr l}"
            | .mdata d b => do
              let bi ← intern b
              pure s!"mdata {repr d} {bi}"
            | .proj n i b => do
              let bi ← intern b
              pure s!"proj {repr n} {i} {bi}"
          liftM <| stream.putStrLn s!"NODE {id} {payload}"
        liftM <| stream.putStrLn "END_DECL"
      let _ ← liftIO <| action.run ({}, #[])
      if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial declaration {name}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "unapproved axiom {ax} in {name}"
  liftIO <| stream.putStrLn s!"TOTAL_LOCAL_DECLARATIONS {count}"
  liftIO handle.flush
