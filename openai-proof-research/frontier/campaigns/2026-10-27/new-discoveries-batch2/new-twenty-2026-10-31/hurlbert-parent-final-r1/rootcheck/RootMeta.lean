import Endpoints
import Control
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let pkt := (← IO.FS.readFile "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/hurlbert-parent-final-r1/rootcheck/order.txt").splitOn "\n" |>.filter (· ≠ "")
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
  let mut stack : Array Name := #[`MathDB356266.conjecture_false]
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
  logInfo m!"ROOT_CLOSURE endpoint=MathDB356266.conjecture_false local_reachable={reach} flagged_reachable={badReach} steps={steps}"
#print axioms MathDB356266.conjecture_false
#check @MathDB356266.conjecture_false
#print axioms MathDB356266.conjectureLinear_false
#check @MathDB356266.conjectureLinear_false
#print MathDB356266.Conjecture
#print MathDB356266.ConjectureLinear
#print MathDB356266.EulerOrdering
#print MathDB356266.Overlaps
#print MathDB356266.Realizes
#print MathDB356266.position
#print MathDB356266.next
#print MathDB356266.Permutation
