import Code
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut count := 0
  let mut bad := 0
  for (n, ci) in env.constants.toList do
    if (env.getModuleIdxFor? n).any (fun idx => env.header.moduleNames[idx.toNat]! == `Code) then
      count := count + 1
      let ax ← collectAxioms n
      let imp := (Compiler.getImplementedBy? env n).isSome
      let ext := (getExternAttrData? env n).isSome
      let denied := ci.isUnsafe || ci.isPartial || imp || ext || n.toString.endsWith "_unsafe_rec" || ax.any (fun a => !(#[``propext, ``Classical.choice, ``Quot.sound]).contains a)
      if denied then bad := bad + 1
      IO.println s!"DECL {n} unsafe={ci.isUnsafe} partial={ci.isPartial} implemented_by={imp} extern={ext} axioms={ax} denied={denied}"
  IO.println s!"TOTAL {count}; DENIED {bad}"
#print CodeCounterexample.source_conjecture_refuted
#print CodeCounterexample.QuasiGroupCode
#print CodeCounterexample.paut
#print CodeCounterexample.C
#print CodeCounterexample.G
#print CodeCounterexample.act
#print CodeCounterexample.codeIso
#print axioms CodeCounterexample.source_conjecture_refuted
#print axioms CodeCounterexample.mem_C
#print axioms CodeCounterexample.preserves_pairs
#print axioms CodeCounterexample.perm_classify
#print axioms CodeCounterexample.auto_classification
#print axioms CodeCounterexample.swap_test
#print axioms CodeCounterexample.sigma_auto
