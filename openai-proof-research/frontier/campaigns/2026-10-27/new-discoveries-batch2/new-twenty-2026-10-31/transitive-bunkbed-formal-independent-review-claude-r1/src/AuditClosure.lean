import BunFinalModel
import Lean

open Lean Elab Command

#print axioms Bun.bunkbed_E7_transitive
#print axioms Bun.card_token
#print axioms Bun.card_out
#print axioms Bun.prob_layer_true_le_false

#check @Bun.bunkbed_E7_transitive
set_option pp.explicit true in
#check @Bun.bunkbed_E7_transitive
#print HToken
#print Token
#print Vert
#print Out
#print Arc
#print Reach

namespace AuditClosure

/-- Constants referenced by a constant, including the structural links of inductive types. -/
def directDeps (c : ConstantInfo) : Array Name :=
  let base : Array Name := c.type.getUsedConstants
  let extra : Array Name := match c with
    | .defnInfo v => v.value.getUsedConstants
    | .thmInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | .inductInfo v => v.ctors.toArray ++ v.all.toArray
    | .ctorInfo v => #[v.induct]
    | .recInfo v => v.all.toArray ++ (v.rules.toArray.flatMap fun r => r.rhs.getUsedConstants)
    | _ => #[]
  base ++ extra

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

end AuditClosure

open AuditClosure in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[``Bun.bunkbed_E7_transitive]
  let mut missing : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then
      continue
    seen := seen.insert n
    match env.find? n with
    | none => missing := missing.push n
    | some c =>
      for d in directDeps c do
        if !seen.contains d then
          stack := stack.push d
  let mut total : Nat := 0
  let mut axioms : Array Name := #[]
  let mut unsafeC : Array Name := #[]
  let mut partialC : Array Name := #[]
  let mut implBy : Array (Name × Name) := #[]
  let mut externC : Array Name := #[]
  let mut opaqueC : Array Name := #[]
  let mut kinds : Std.HashMap String Nat := {}
  let mut mods : Std.HashMap String Nat := {}
  let mut bunC : Array Name := #[]
  for n in seen do
    total := total + 1
    let some c := env.find? n | continue
    let k := kindName c
    kinds := kinds.insert k ((kinds.getD k 0) + 1)
    match c with
    | .axiomInfo _ => axioms := axioms.push n
    | .opaqueInfo _ => opaqueC := opaqueC.push n
    | _ => pure ()
    if c.isUnsafe then
      unsafeC := unsafeC.push n
    if c.isPartial then
      partialC := partialC.push n
    match Lean.Compiler.getImplementedBy? env n with
    | some t => implBy := implBy.push (n, t)
    | none => pure ()
    if Lean.isExtern env n then
      externC := externC.push n
    let modName : String := match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => "<this-module>"
    let isOurs := (modName.startsWith "Bun")
    let key := if isOurs then modName else (match modName.splitOn "." with | a :: _ => a | [] => modName)
    mods := mods.insert key ((mods.getD key 0) + 1)
    if isOurs then
      bunC := bunC.push n
  logInfo m!"TOTAL closure constants: {total}; missing: {missing.size} {missing}"
  logInfo m!"KINDS: {kinds.toList}"
  logInfo m!"BY MODULE ROOT: {mods.toList}"
  logInfo m!"AXIOMS ({axioms.size}): {axioms}"
  logInfo m!"UNSAFE ({unsafeC.size}): {unsafeC}"
  logInfo m!"PARTIAL ({partialC.size}): {partialC}"
  logInfo m!"IMPLEMENTED_BY ({implBy.size}): {implBy}"
  logInfo m!"EXTERN ({externC.size}): {externC}"
  logInfo m!"OPAQUE ({opaqueC.size}): {opaqueC}"
  logInfo m!"BUN-MODULE CONSTANTS IN CLOSURE: {bunC.size}"
