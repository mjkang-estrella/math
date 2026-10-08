import Research.WordQueryCode
import Research.WordRun
import Research.IndexedLookup

/-! Compiled checks of actual fresh runs, not kernel correctness proofs or
performance comparisons. All budgets/setup/prefixRun costs come from the frozen
challenge, and all measured counts are projections of actual runner traces. -/
open Research WordCore WordQueryData WordQueryCode WordRun

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def checkCase (W k : Nat) (pairs : Array (Nat × Nat)) (x : Nat) : IO Nat := do
  let s : Sizes := ⟨W, pairs.size, k⟩
  if h : Admissible s then
    if hx : x < 2 ^ k then
      if he : ∀ i : Fin pairs.size, (pairs[i]).1 < 2 ^ k ∧ (pairs[i]).2 < s.U then
        let es : Vector (WordQueryData.Entry s) s.m := Vector.ofFn fun i =>
          ⟨⟨(pairs[i]).1, (he i).1⟩, ⟨(pairs[i]).2, (he i).2⟩⟩
        let d : Data s := ⟨es, ⟨x, hx⟩⟩
        check (decide (∀ i j : Fin pairs.size, i.val ≤ j.val →
          (pairs[i]).1 ≤ (pairs[j]).1)) "unsorted test input"
        let raw := rawInput d
        let P := profile s h.1
        let a := 6 * s.L + 26 * s.m + 42
        let prefixFuel := s.I + a
        let initialBits := (encode d).map (fun b => if b then 1 else 0)
        let expectedHeap := initialBits ++ [0, 0] ++ pairs.toList.flatMap
          (fun e => [e.1, e.2]) ++ [s.m, k, x, 0]
        let lastPair := pairs.back?
        let c := s.queryStart
        let lastBit := if 0 < k then x % 2 else (lastPair.map (·.2)).getD 0 % 2
        let expectedRegs := [0, 1, 2, W, s.m, k, s.L, k, c, x, lastBit, s.L,
          s.B, s.A, s.m, (lastPair.map (·.1)).getD 0, (lastPair.map (·.2)).getD 0,
          x, 0, 0, 0, 0, 0, 0, 0, s.A+2, s.L, c, 0, 0, 0, 0]
        let before := pairs.toList.takeWhile (fun e => e.1 < x)
        let candidate := pairs[before.length]?
        let linearFound := candidate.bind (fun e => if e.1 == x then some e.2 else none)
        let linearProbes := before.length + (if candidate.isSome then 1 else 0)
        let linearCost := if candidate.isSome then 10 * linearProbes + 7 else 10 * s.m + 10
        let oracle := IndexedLookup.lookup (pairs.map fun e => ⟨e.1, e.2⟩) x
        let binaryFound ← match oracle.outcome with
          | .found payload => pure (some payload)
          | .absent => pure none
          | .exhausted => throw (IO.userError "reference lookup exhausted")
        let binaryCost := 13 * oracle.probes + (if binaryFound.isSome then 8 else 11)
        let mut total := 0
        let mut prefixes : List (List (WordRun.Event P)) := []
        for (name, code, found, probes, searchCost) in
            [("linear", linear s h, linearFound, linearProbes, linearCost),
             ("binary", binary s h, binaryFound, oracle.probes, binaryCost)] do
          let prefixRun := run P code raw prefixFuel
          total := total + prefixRun.used
          match prefixRun.stop with
          | .exhausted (.guest st) =>
              check (st.pc.val == 86 && prefixRun.remaining == 0 && prefixRun.used == prefixFuel)
                s!"{name} prefixRun boundary"
              check ((st.regs.toList.map Fin.val) == expectedRegs) s!"{name} prefixRun registers"
              check ((st.heap.toList.map Fin.val) == expectedHeap) s!"{name} prefixRun heap"
          | _ => throw (IO.userError s!"{name} prefixRun did not exhaust at guest boundary")
          let pl := prefixRun.ledger
          check (pl.clearRegisters == 32 && pl.clearHeap == s.M && pl.inputCopies == s.L &&
            pl.guestAttempts == a && pl.completedLoads == s.L && pl.completedStores == 2*s.m+3)
            s!"{name} prefixRun setup/access ledger"
          let expectedOps := [(Opcode.const,9), (.mov,12*s.m+19), (.add,s.L+5*s.m+3),
            (.sub,s.L), (.mul,s.L+s.m), (.lt,s.L+3*s.m+4), (.branch,s.L+3*s.m+4),
            (.load,s.L), (.store,2*s.m+3), (.eq,0), (.divmod,0), (.jump,0), (.halt,0)]
          check (expectedOps.all fun p => pl.opcodeAttempts p.1 == p.2) s!"{name} prefixRun opcodes"
          prefixes := prefixRun.trace :: prefixes
          let r := run P code raw s.F
          total := total + r.used
          let expectedOutput := if let some payload := found then [1,payload] else [0,0]
          check ((output r).map (fun v => v.toList.map Fin.val) == some expectedOutput)
            s!"{name} output W={W} k={k} m={s.m} x={x}"
          match r.stop with
          | .halted st =>
              check ((st.heap.toList.map Fin.val).take s.L == initialBits &&
                (st.regs.toList.map Fin.val).head? == some 0) s!"{name} source/r0 preservation"
          | _ => throw (IO.userError s!"{name} did not halt")
          check (r.used == prefixFuel + searchCost && r.remaining + r.used == s.F &&
            r.ledger.guestAttempts == a+searchCost && r.ledger.opcodeAttempts .eq == probes &&
            r.ledger.opcodeAttempts .halt == 1 && r.ledger.invalidPCAttempts == 0 &&
            r.ledger.completedLoads == s.L+2+probes+(if found.isSome then 1 else 0) &&
            r.ledger.completedStores == 2*s.m+5) s!"{name} fresh-run ledger/path"
          check (decide (r.trace.take prefixFuel = prefixRun.trace)) s!"{name} actual prefixRun trace"
        match prefixes with
        | [left,right] => check (decide (left = right)) "common actual prefixRun traces"
        | _ => throw (IO.userError "expected two prefixes")
        return total
      else throw (IO.userError "entry outside bounded data domain")
    else throw (IO.userError "query outside bounded data domain")
  else throw (IO.userError "test profile rejected by actual common admission")

private def stopTag {P : Profile} (r : WordRun.Result P) : Nat :=
  match r.stop with
  | .halted _ => 0
  | .faulted _ _ => 1
  | .exhausted (.setup _) => 2
  | .exhausted (.guest _) => 3

private def boundaryChecks : IO Nat := do
  let s : Sizes := ⟨7,0,0⟩
  let h := accepted_7_0_0
  let P := profile s h.1
  let raw := rawInput (zeroData s)
  let mut events := 0
  for code in [linear s h, binary s h] do
    let full := run P code raw s.F
    events := events + full.used
    for fuel in [0,s.I-1,s.I,s.I+1,s.I+(6*s.L+42),full.used-1,full.used,full.used+9] do
      let r := run P code raw fuel
      events := events + r.used
      let expectedTag := if fuel < s.I then 2 else if fuel < full.used then 3 else 0
      check (stopTag r == expectedTag && r.used == min fuel full.used &&
        r.used+r.remaining == fuel) s!"fresh fuel boundary {fuel}"
      if full.used ≤ fuel then
        check (decide (r.trace = full.trace) &&
          (output r).map (fun v => v.toList.map Fin.val) ==
            (output full).map (fun v => v.toList.map Fin.val)) "terminal stability"
  return events

#eval do
  let mut events := 0
  let mut cases : List (Nat × Nat × Array (Nat × Nat) × Nat) := []
  -- Complete data domains for these selected public profiles, not all profiles.
  for k in [0,7] do
    for x in List.range (2^k) do
      cases := (7,k,#[],x) :: cases
  for payload in List.range 128 do
    cases := (7,0,#[(0,payload)],0) :: cases
  -- Targeted boundary, duplicate and absence cases; these domains are not exhaustive.
  let shapes : List (Nat × Array Nat) := [(7,#[0]),(7,#[127]),(1,#[0,0]),(1,#[1,1]),(2,#[0,2,2]),
      (7,#[0,1,63,64,126,127]),(0,Array.replicate 12 0)]
  for shape in shapes do
    let k : Nat := (shape : Nat × Array Nat).1
    let keys : Array Nat := (shape : Nat × Array Nat).2
    for variant in ([0,1] : List Nat) do
      let pairs := keys.mapIdx fun j key => (key, if (j+variant)%2 == 1 then 127 else 0)
      let queries := ([0,2^k-1] ++ keys.toList ++
        [1,2,62,63,64,65,126].filter (fun v => v < 2^k)).eraseDups
      for x in queries do
        cases := (7,k,pairs,x) :: cases
  check (cases.length == 329) "dataset construction count"
  for (W,k,es,x) in cases do
    events := events + (← checkCase W k es x)
    check (events < 1000000) "event ceiling exceeded"
  events := events + (← boundaryChecks)
  check (events < 1000000) "event ceiling exceeded"
  IO.println s!"PASS: {cases.length} paired datasets, {4*cases.length+18} actual fresh runs, {events} setup/guest trace events. Full domains (W,m,k)=(7,0,0),(7,0,7),(7,1,0); other cases targeted. Includes prefix states/traces/opcodes, output/IndexedLookup checks, fresh ledgers, fuel boundaries. Finite execution checks only."
