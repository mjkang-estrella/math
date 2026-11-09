import Endpoint
import Control
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt := (← IO.FS.readFile "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/hetyei-parent-final-r1/rootcheck/order.txt").splitOn "\n" |>.filter (· ≠ "")
  let isLocal : Name → Bool := fun c => match env.getModuleIdxFor? c with
    | some idx => pkt.contains (env.header.moduleNames[idx.toNat]!).toString
    | none => false
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if isLocal c then
      n := n + 1
      if ci.isUnsafe || ci.isPartial then bad := bad.push c
      if (Lean.Compiler.getImplementedBy? env c).isSome then bad := bad.push c
      if Lean.isExtern env c then bad := bad.push c
      if (c.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push c
  logInfo m!"ROOT_META packet_modules={pkt.length} local={n} flagged={bad}"
  let mut stack : Array Name := #[`Hetyei347230.kernel_conjecture_false]
  let mut seen : NameSet := {}
  let mut reach : Nat := 0
  let mut badReach : Array Name := #[]
  let mut steps : Nat := 0
  while stack.size > 0 && steps < 1000000 do
    steps := steps + 1
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if !isLocal c then continue
    reach := reach + 1
    if bad.contains c then badReach := badReach.push c
    match env.find? c with
    | none => badReach := badReach.push c
    | some ci =>
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
      for u in used do
        if !seen.contains u then stack := stack.push u
  logInfo m!"ROOT_CLOSURE endpoint=Hetyei347230.kernel_conjecture_false local_reachable={reach} flagged_reachable={badReach} steps={steps}"
#print axioms Hetyei347230.kernel_conjecture_false
#check @Hetyei347230.kernel_conjecture_false
#print Hetyei347230.KernelConjecture
#print Hetyei347230.anti
#print Hetyei347230.deg
#print Hetyei347230.star
#print Hetyei347230.I2
#print Hetyei347230.I2w
#print Hetyei347230.Mw
#print Hetyei347230.Mrs
#print Hetyei347230.MrsAux
#print Hetyei347230.cop
#print Hetyei347230.inIndex
