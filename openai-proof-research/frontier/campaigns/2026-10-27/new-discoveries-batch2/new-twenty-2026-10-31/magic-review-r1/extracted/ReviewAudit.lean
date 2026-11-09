import Magic
import Lean
open Lean Elab Command
set_option pp.universes true
set_option pp.fullNames true
run_cmd do
 let env ← getEnv
 let mut count : Nat := 0
 for (n,c) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  if env.header.moduleNames[idx.toNat]! != `Magic then continue
  count := count + 1
  let axs ← Lean.collectAxioms n
  let tp ← liftTermElabM <| Meta.ppExpr c.type
  logInfo m!"DECL|{n}|module=Magic|unsafe={c.isUnsafe}|partial={c.isPartial}|body={(c.value? (allowOpaque := true)).isSome}|axioms={axs.toList}|TYPE={tp}"
  if c.isUnsafe || c.isPartial || (c.value? (allowOpaque := true)).isNone then throwError "bad declaration {n}"
  for a in axs do
   unless [``propext, ``Classical.choice, ``Quot.sound].contains a do throwError "bad axiom {a}"
 logInfo m!"COUNT|{count}"
#print Magic381805.strength
#print Magic381805.SourceConjecture
#print Magic381805.IsFamily
#print Magic381805.IsSuperEdgeMagic
#print axioms Magic381805.source_refutation
example : Magic381805.vertexLabel 6 = 1 := by decide
example : ¬ Magic381805.G.Adj 0 2 := by decide
example : ¬ Magic381805.IsSuperEdgeMagic Magic381805.G 11 11 27 Magic381805.labelEquiv := by
 unfold Magic381805.IsSuperEdgeMagic
 decide
