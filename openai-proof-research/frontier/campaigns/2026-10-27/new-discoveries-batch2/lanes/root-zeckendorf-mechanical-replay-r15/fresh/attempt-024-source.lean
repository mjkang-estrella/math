import Lean.Environment
import Lean.Util.Path
import Lean.Util.FoldConsts
set_option autoImplicit false
open Lean

def ownedModules : List Name :=
  [`Literal, `Terminal, `Law, `Cells, `Product, `Prefix, `Marks, `Boards,
   `Injection, `Abundance, `Tail, `Concentration, `Assembly, `LastSplit,
   `SuffixUnion, `Growth, `Uniform, `UniformSuffix, `Observables, `FiniteProbability, `Measurability, `Median, `AllN, `Endpoint]

def inspectGraph (env : Environment) (roots : Array Name) : IO (NameSet × NameSet) := do
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if !seen.contains name then
      seen := seen.insert name
      let some info := env.find? name | throw (IO.userError s!"REJECTED missing {name}")
      if info.isUnsafe then throw (IO.userError s!"REJECTED unsafe {name}")
      match info with
      | .defnInfo v =>
        if v.safety == .partial then throw (IO.userError s!"REJECTED partial {name}")
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throw (IO.userError s!"REJECTED axiom {name}")
        axioms := axioms.insert name
      | _ => pure ()
      todo := todo ++ info.type.getUsedConstants
      if let some body := info.value? (allowOpaque := true) then
        todo := todo ++ body.getUsedConstants
  return (seen, axioms)

def main : IO Unit := do
  initSearchPath "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux"
  let env ← importModules #[{module := `Endpoint}] {} (loadExts := false)
  let mut roots : Array Name := #[]
  for idx in [:env.header.moduleData.size] do
    let modName := env.header.moduleNames[idx]!
    if ownedModules.contains modName then
      for name in env.header.moduleData[idx]!.constNames do
        let some info := env.find? name | throw (IO.userError s!"REJECTED missing origin {name}")
        let partialFlag := match info with
          | .defnInfo v => v.safety == .partial
          | _ => false
        IO.println s!"OWN_DECL {name}"
        IO.println s!"OWN_MODULE {name} {modName}"
        IO.println s!"OWN_SAFETY {name} {info.isUnsafe}"
        IO.println s!"OWN_PARTIAL {name} {partialFlag}"
        if info.isUnsafe || partialFlag then throw (IO.userError s!"REJECTED origin {name}")
        roots := roots.push name
  let (seen, _) ← inspectGraph env roots
  IO.println s!"TRANSITIVE_SAFE_COUNT {seen.size}"
  for name in roots do
    let (_, axs) ← inspectGraph env #[name]
    let names := axs.toArray.qsort Name.lt
    if names.isEmpty then IO.println s!"'{name}' does not depend on any axioms"
    else IO.println s!"'{name}' depends on axioms: [{String.intercalate ", " (names.toList.map toString)}]"
