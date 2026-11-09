import CaterpillarCenter
open Lean Elab Command

/- Enumerate every constant whose defining module is `CaterpillarCenter` (including generated
auxiliary declarations), print its transitive axioms, and fail on anything outside the allowed set,
on `sorryAx`, or on unsafe/partial declarations. -/
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `CaterpillarCenter | throwError "module not found"
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

#print axioms Caterpillar366834.not_caterpillarCenterConjecture
#print axioms Caterpillar366834.not_caterpillarCenterConjectureWeak
#print axioms Caterpillar366834.witness
#check @Caterpillar366834.CaterpillarCenterConjecture
#print Caterpillar366834.CaterpillarCenterConjecture
#print Caterpillar366834.CaterpillarCenterConjectureWeak
#print Caterpillar366834.IsCaterpillar
#print Caterpillar366834.starSize
#print Caterpillar366834.IsMaxCenter
#print Caterpillar366834.W
#print Caterpillar366834.edges
