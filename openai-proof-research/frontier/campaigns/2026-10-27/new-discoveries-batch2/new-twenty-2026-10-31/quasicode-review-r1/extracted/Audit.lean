import Code
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`CodeCounterexample).isPrefixOf n then
      names := names.push n
      match ci with
      | .axiomInfo _ => IO.println s!"LOCAL AXIOM {n}"
      | .opaqueInfo _ => IO.println s!"LOCAL OPAQUE {n}"
      | _ => pure ()
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut bad := 0
  for n in sorted do
    let ax ← collectAxioms n
    IO.println s!"DECL {n}: {ax}"
    if ax.any (fun a => !allowed.contains a) then
      bad := bad + 1
      IO.println s!"BAD {n}: {ax}"
  IO.println s!"audited {sorted.size} local declarations (incl. generated); declarations with non-allowed axioms: {bad}"
#print axioms CodeCounterexample.source_conjecture_refuted
