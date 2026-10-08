import Research.WordRun

/-! Executable raw-input checks on hand-specified small programs. These are
compiled evaluations, not kernel proofs or timing measurements. Each asserted
fuel/setup/guest count is computed independently from the program schedule. -/
open Research.WordCore Research.WordRun

private def p : Profile := ⟨3, 2, 4, 2, 1, by decide, by decide, by decide, by decide⟩
private instance : NeZero p.bound := ⟨by decide⟩
private instance : NeZero p.R := ⟨by decide⟩
private def input (i : Fin p.L) : Bool := i.val == 0

private def copyCode : Program p :=
  ⟨#[.const 0 0 1, .load 1 0 2, .const 0 2 3, .store 0 1 4, .halt], by decide⟩
private def faultCode : Program p := ⟨#[.const 0 4 1, .load 1 0 2], by decide⟩
private def storeCode : Program p := ⟨#[.const 0 2 1, .store 0 0 7], by decide⟩
private def loopCode : Program p := ⟨#[.jump 0], by decide⟩
private def emptyCode : Program p := ⟨#[], by decide⟩
private def countdownCode : Program p :=
  ⟨#[.const 0 2 1, .const 1 1 2, .sub 0 0 1 3, .branch 0 4 2, .halt], by decide⟩

private def stopTag (r : Result p) : Nat :=
  match r.stop with
  | .halted _ => 0
  | .faulted _ _ => 1
  | .exhausted (.setup _) => 2
  | .exhausted (.guest _) => 3

private def observableOutput (r : Result p) : Option Nat :=
  (output r).map (fun v => (v.get ⟨0, by decide⟩).val)

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

#eval do
  -- I=2 register clears+4 heap clears+2 input copies=8. Halt is attempt 5.
  for fuel in List.range 17 do
    let r := run p copyCode input fuel
    let expectedSetup := min fuel 8
    let expectedGuest := min (fuel - 8) 5
    let expectedUsed := expectedSetup + expectedGuest
    let expectedTag := if fuel < 8 then 2 else if fuel < 13 then 3 else 0
    check (stopTag r == expectedTag && r.used == expectedUsed &&
      r.remaining == fuel - expectedUsed && r.ledger.setupUnits == expectedSetup &&
      r.ledger.guestAttempts == expectedGuest) s!"copy fuel boundary {fuel}"
    check (observableOutput r == (if fuel < 13 then none else some 1))
      s!"copy output boundary {fuel}"
  let copied := run p copyCode input 20
  check (copied.ledger.clearRegisters == 2 && copied.ledger.clearHeap == 4 &&
    copied.ledger.inputCopies == 2 && copied.ledger.completedLoads == 1 &&
    copied.ledger.completedStores == 1 && copied.ledger.opcodeAttempts .const == 2 &&
    copied.ledger.opcodeAttempts .halt == 1) "copy ledger"
  let badLoad := run p faultCode input 20
  check (stopTag badLoad == 1 && badLoad.used == 10 && badLoad.remaining == 10 &&
    badLoad.ledger.opcodeAttempts .load == 1 && badLoad.ledger.completedLoads == 0 &&
    badLoad.ledger.invalidPCAttempts == 0 && observableOutput badLoad == none)
    "failed load attempts/completions"
  let stored := run p storeCode input 20
  check (stopTag stored == 1 && stored.used == 11 && stored.remaining == 9 &&
    stored.ledger.completedStores == 1 && stored.ledger.invalidPCAttempts == 1)
    "store then invalid fetch ledger"
  match stored.stop with
  | .faulted .invalidPC s =>
      check ((s.heap.get ⟨2, by decide⟩).val == 2 && s.pc.val == 7)
        "committed store survives invalid fetch"
  | _ => throw (IO.userError "expected invalid-PC fault")
  for fuel in List.range 25 do
    let r := run p loopCode input fuel
    check (r.used == fuel && r.remaining == 0 &&
      r.ledger.opcodeAttempts .jump == fuel - 8 &&
      stopTag r == (if fuel < 8 then 2 else 3)) s!"loop fuel {fuel}"
  for fuel in List.range 19 do
    let r := run p countdownCode input fuel
    let used := min fuel 15
    check (r.used == used && r.remaining == fuel - used &&
      stopTag r == (if fuel < 8 then 2 else if fuel < 15 then 3 else 0))
      s!"conditional countdown fuel {fuel}"
  let counted := run p countdownCode input 21
  check (counted.ledger.opcodeAttempts .const == 2 &&
    counted.ledger.opcodeAttempts .sub == 2 && counted.ledger.opcodeAttempts .branch == 2 &&
    counted.ledger.opcodeAttempts .halt == 1 && counted.ledger.guestAttempts == 7 &&
    counted.remaining == 6 && observableOutput counted == some 0)
    "conditional countdown exact opcode counts"
  let empty := run p emptyCode input 9
  check (stopTag empty == 1 && empty.used == 9 && empty.ledger.setupUnits == 8 &&
    empty.ledger.invalidPCAttempts == 1 && empty.ledger.opcodeAttempts .halt == 0)
    "empty code pays setup and invalid attempt"
  IO.println "PASS: raw copy 17 fuel budgets; loop 25 fuel budgets; conditional countdown 19 fuel budgets; load fault; committed store/invalid fetch; empty code; actual ledger/output checks."
