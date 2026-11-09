import EndpointR5
import Lean.Util.CollectAxioms
open Lean
set_option maxHeartbeats 0
namespace AuditR5
abbrev Store := Lean.ExprStructMap Nat × Array String

def encode (fuel : Nat) : Expr → StateM Store Nat :=
  Nat.rec
    (fun _ => do
      let id := (← get).2.size
      modify fun (memo, rows) => (memo, rows.push "FUEL_EXHAUSTED")
      return id)
    (fun _ recur e => do
      if let some id := (← get).1.get? ⟨e⟩ then return id
      let row ← match e with
        | .bvar i => pure s!"bvar {i}"
        | .fvar i => pure s!"fvar {reprStr i}"
        | .mvar i => pure s!"mvar {reprStr i}"
        | .sort l => pure s!"sort {reprStr l}"
        | .const n ls => pure s!"const {reprStr n} {reprStr ls}"
        | .app f a => do
            let f ← recur f
            let a ← recur a
            pure s!"app {f} {a}"
        | .lam n t b bi => do
            let t ← recur t
            let b ← recur b
            pure s!"lam {reprStr n} {t} {b} {reprStr bi}"
        | .forallE n t b bi => do
            let t ← recur t
            let b ← recur b
            pure s!"forallE {reprStr n} {t} {b} {reprStr bi}"
        | .letE n t v b nd => do
            let t ← recur t
            let v ← recur v
            let b ← recur b
            pure s!"letE {reprStr n} {t} {v} {b} {nd}"
        | .lit v => pure s!"lit {reprStr v}"
        | .mdata md b => do
            let b ← recur b
            pure s!"mdata {reprStr md} {b}"
        | .proj n i b => do
            let b ← recur b
            pure s!"proj {reprStr n} {i} {b}"
      let id := (← get).2.size
      modify fun (memo, rows) => (memo.insert ⟨e⟩ id, rows.push row)
      return id
    )
    fuel
end AuditR5
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if m.toString.startsWith "Audit" then
      throwError "Audit module inside proof import closure: {m}"
  let mut count := 0
  let mut store : AuditR5.Store := ({}, #[])
  for (n, ci) in env.constants.toList do
    let modName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if modName ∈ [`BridgeR3, `Canonical, `ChecksR3_0000_0, `ChecksR3_0001_0, `ChecksR3_0002_0, `ChecksR3_0010_0, `ChecksR3_0011_0, `ChecksR3_0012_0, `ChecksR3_0020_0, `ChecksR3_0021_0, `ChecksR3_0022_0, `ChecksR3_0100_0, `ChecksR3_0101_0, `ChecksR3_0102_0, `ChecksR3_0110_0, `ChecksR3_0111_0, `ChecksR3_0112_0, `ChecksR3_0120_0, `ChecksR3_0121_0, `ChecksR3_0122_0, `ChecksR3_0122_1, `ChecksR3_0200_0, `ChecksR3_0201_0, `ChecksR3_0202_0, `ChecksR3_0210_0, `ChecksR3_0211_0, `ChecksR3_0212_0, `ChecksR3_0212_1, `ChecksR3_0220_0, `ChecksR3_0221_0, `ChecksR3_0221_1, `ChecksR3_0222_0, `ChecksR3_0222_1, `ChecksR3_0222_2, `ChecksR3_0222_3, `ChecksR3_1000_0, `ChecksR3_1001_0, `ChecksR3_1002_0, `ChecksR3_1010_0, `ChecksR3_1011_0, `ChecksR3_1012_0, `ChecksR3_1020_0, `ChecksR3_1021_0, `ChecksR3_1022_0, `ChecksR3_1022_1, `ChecksR3_1100_0, `ChecksR3_1101_0, `ChecksR3_1102_0, `ChecksR3_1110_0, `ChecksR3_1111_0, `ChecksR3_1112_0, `ChecksR3_1112_1, `ChecksR3_1120_0, `ChecksR3_1121_0, `ChecksR3_1121_1, `ChecksR3_1122_0, `ChecksR3_1122_1, `ChecksR3_1122_2, `ChecksR3_1122_3, `ChecksR3_1200_0, `ChecksR3_1201_0, `ChecksR3_1202_0, `ChecksR3_1202_1, `ChecksR3_1210_0, `ChecksR3_1211_0, `ChecksR3_1211_1, `ChecksR3_1212_0, `ChecksR3_1212_1, `ChecksR3_1212_2, `ChecksR3_1212_3, `ChecksR3_1220_0, `ChecksR3_1220_1, `ChecksR3_1221_0, `ChecksR3_1221_1, `ChecksR3_1221_2, `ChecksR3_1221_3, `ChecksR3_1222_0, `ChecksR3_1222_1, `ChecksR3_1222_2, `ChecksR3_1222_3, `ChecksR3_1222_4, `ChecksR3_1222_5, `ChecksR3_1222_6, `ChecksR3_1222_7, `ChecksR3_2000_0, `ChecksR3_2001_0, `ChecksR3_2002_0, `ChecksR3_2010_0, `ChecksR3_2011_0, `ChecksR3_2012_0, `ChecksR3_2012_1, `ChecksR3_2020_0, `ChecksR3_2021_0, `ChecksR3_2021_1, `ChecksR3_2022_0, `ChecksR3_2022_1, `ChecksR3_2022_2, `ChecksR3_2022_3, `ChecksR3_2100_0, `ChecksR3_2101_0, `ChecksR3_2102_0, `ChecksR3_2102_1, `ChecksR3_2110_0, `ChecksR3_2111_0, `ChecksR3_2111_1, `ChecksR3_2112_0, `ChecksR3_2112_1, `ChecksR3_2112_2, `ChecksR3_2112_3, `ChecksR3_2120_0, `ChecksR3_2120_1, `ChecksR3_2121_0, `ChecksR3_2121_1, `ChecksR3_2121_2, `ChecksR3_2121_3, `ChecksR3_2122_0, `ChecksR3_2122_1, `ChecksR3_2122_2, `ChecksR3_2122_3, `ChecksR3_2122_4, `ChecksR3_2122_5, `ChecksR3_2122_6, `ChecksR3_2122_7, `ChecksR3_2200_0, `ChecksR3_2201_0, `ChecksR3_2201_1, `ChecksR3_2202_0, `ChecksR3_2202_1, `ChecksR3_2202_2, `ChecksR3_2202_3, `ChecksR3_2210_0, `ChecksR3_2210_1, `ChecksR3_2211_0, `ChecksR3_2211_1, `ChecksR3_2211_2, `ChecksR3_2211_3, `ChecksR3_2212_0, `ChecksR3_2212_1, `ChecksR3_2212_2, `ChecksR3_2212_3, `ChecksR3_2212_4, `ChecksR3_2212_5, `ChecksR3_2212_6, `ChecksR3_2212_7, `ChecksR3_2220_0, `ChecksR3_2220_1, `ChecksR3_2220_2, `ChecksR3_2220_3, `ChecksR3_2221_0, `ChecksR3_2221_1, `ChecksR3_2221_2, `ChecksR3_2221_3, `ChecksR3_2221_4, `ChecksR3_2221_5, `ChecksR3_2221_6, `ChecksR3_2221_7, `ChecksR3_2222_0, `ChecksR3_2222_1, `ChecksR3_2222_10, `ChecksR3_2222_11, `ChecksR3_2222_12, `ChecksR3_2222_13, `ChecksR3_2222_14, `ChecksR3_2222_15, `ChecksR3_2222_2, `ChecksR3_2222_3, `ChecksR3_2222_4, `ChecksR3_2222_5, `ChecksR3_2222_6, `ChecksR3_2222_7, `ChecksR3_2222_8, `ChecksR3_2222_9, `Concrete, `ConcreteR2, `Definitions, `EvalR3_0000, `EvalR3_0001, `EvalR3_0002, `EvalR3_0010, `EvalR3_0011, `EvalR3_0012, `EvalR3_0020, `EvalR3_0021, `EvalR3_0022, `EvalR3_0100, `EvalR3_0101, `EvalR3_0102, `EvalR3_0110, `EvalR3_0111, `EvalR3_0112, `EvalR3_0120, `EvalR3_0121, `EvalR3_0122, `EvalR3_0200, `EvalR3_0201, `EvalR3_0202, `EvalR3_0210, `EvalR3_0211, `EvalR3_0212, `EvalR3_0220, `EvalR3_0221, `EvalR3_0222, `EvalR3_1000, `EvalR3_1001, `EvalR3_1002, `EvalR3_1010, `EvalR3_1011, `EvalR3_1012, `EvalR3_1020, `EvalR3_1021, `EvalR3_1022, `EvalR3_1100, `EvalR3_1101, `EvalR3_1102, `EvalR3_1110, `EvalR3_1111, `EvalR3_1112, `EvalR3_1120, `EvalR3_1121, `EvalR3_1122, `EvalR3_1200, `EvalR3_1201, `EvalR3_1202, `EvalR3_1210, `EvalR3_1211, `EvalR3_1212, `EvalR3_1220, `EvalR3_1221, `EvalR3_1222, `EvalR3_2000, `EvalR3_2001, `EvalR3_2002, `EvalR3_2010, `EvalR3_2011, `EvalR3_2012, `EvalR3_2020, `EvalR3_2021, `EvalR3_2022, `EvalR3_2100, `EvalR3_2101, `EvalR3_2102, `EvalR3_2110, `EvalR3_2111, `EvalR3_2112, `EvalR3_2120, `EvalR3_2121, `EvalR3_2122, `EvalR3_2200, `EvalR3_2201, `EvalR3_2202, `EvalR3_2210, `EvalR3_2211, `EvalR3_2212, `EvalR3_2220, `EvalR3_2221, `EvalR3_2222, `GirthR2, `Invariance, `InvarianceR2, `MaskR3, `ReductionR2, `Separation, `StructureR4, `TreeModelsR3, `StructureR5, `CoordinatesR5, `HomR5, `NumberingR5, `EndpointR5, `AuditR5] then
      count := count + 1
      let axs ← collectAxioms n
      let (ty, st) := (AuditR5.encode 10000 ci.type).run store
      store := st
      let mut body := "none"
      if let some value := ci.value? (allowOpaque := true) then
        let (id, st) := (AuditR5.encode 10000 value).run store
        store := st
        body := s!"node {id}"
      logInfo m!"DECL {n}\nMODULE {modName}\nUNSAFE {ci.isUnsafe}\nPARTIAL {ci.isPartial}\nTYPE_NODE {ty}\nBODY {body}\nAXIOMS {axs}"
      if ci.isUnsafe || ci.isPartial then throwError "Forbidden safety flag: {n}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Forbidden axiom {ax} in {n}"
  for i in [:store.2.size] do
    if store.2[i]! == "FUEL_EXHAUSTED" then throwError "Expression fuel exhausted"
    logInfo m!"EXPR_NODE {i} {store.2[i]!}"
  logInfo m!"TOTAL_EXPR_NODES {store.2.size}"
  logInfo m!"TOTAL_LOCAL_DECLARATIONS {count}"
  logInfo "TOTAL_POLICY_VIOLATIONS 0"
