import OrdinalLine
open Lean Elab Command

/- Enumerate every constant whose defining module is `OrdinalLine` (including generated
auxiliary declarations), print its transitive axioms, and fail on anything outside the allowed set,
on `sorryAx`, or on unsafe/partial declarations. -/
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `OrdinalLine | throwError "module not found"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then
      names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some c := env.find? n | throwError "missing {n}"
    if c.isUnsafe then throwError "unsafe declaration {n}"
    if c.isPartial then throwError "partial declaration {n}"
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless allowed.contains a do throwError "disallowed axiom {a} in {n}"
    logInfo s!"LOCAL {n} AXIOMS {axs.toList}"
    count := count + 1
  logInfo s!"TOTAL_LOCAL {count}"

#print axioms OrdinalSpaces366371.not_majorizationConjecture
#print axioms OrdinalSpaces366371.witness
#print OrdinalSpaces366371.MajorizationConjecture
#print OrdinalSpaces366371.IsOrdinalSpace
#print OrdinalSpaces366371.EmbeddableInLine
#print OrdinalSpaces366371.Prec
#print OrdinalSpaces366371.Sim
#print OrdinalSpaces366371.HasMajorization
#print OrdinalSpaces366371.D
#print OrdinalSpaces366371.δW
