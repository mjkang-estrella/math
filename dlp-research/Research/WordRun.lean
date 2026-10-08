import Research.WordCore

/-! W011 fresh-input runner. Logical optional setup cells are indexed by finite
types; their host representation is not a physical memory bound. Only cells
proved initialized can be exposed to the guest. Every charged action contributes
its actual event to the chronological trace. This is no query or solver claim. -/
namespace Research.WordRun

open WordCore

def setupUnits (P : Profile) : Nat := P.R + P.M + P.L
def zeroWord (P : Profile) : Word P := ⟨0, Nat.two_pow_pos _⟩

/-- Internal partial setup state. Readiness witnesses prevent default values
from replacing unwritten cells at the phase boundary. -/
structure PartialState (P : Profile) where
  cursor : Nat
  cursor_bound : cursor ≤ setupUnits P
  regs : Register P → Option (Word P)
  heap : Fin P.M → Option (Word P)
  regs_ready : ∀ r, r.val < cursor → ∃ v, regs r = some v
  heap_ready : ∀ a, P.R + a.val < cursor → ∃ v, heap a = some v

def initialPartial (P : Profile) : PartialState P where
  cursor := 0
  cursor_bound := Nat.zero_le _
  regs := fun _ => none
  heap := fun _ => none
  regs_ready := by intro r h; omega
  heap_ready := by intro a h; omega

inductive Event (P : Profile) where
  | clearRegister (r : Register P)
  | clearHeap (a : Fin P.M)
  | copyInput (i : Fin P.L)
  | guest (event : WordCore.Event P)
  deriving Repr, DecidableEq

/-- Exactly one setup action, selected by the next unperformed action index. -/
def setupStep {P : Profile} (input : Fin P.L → Bool) (s : PartialState P)
    (h : s.cursor < setupUnits P) : PartialState P × Event P :=
  if hr : s.cursor < P.R then
    let r : Register P := ⟨s.cursor, hr⟩
    (⟨s.cursor + 1, by omega,
      (fun x => if x = r then some (zeroWord P) else s.regs x), s.heap,
      (by
        intro x hx
        by_cases he : x = r
        · exact ⟨zeroWord P, by simp [he]⟩
        · have hv : x.val ≠ s.cursor := by intro hh; apply he; exact Fin.ext hh
          obtain ⟨v, hv⟩ := s.regs_ready x (by omega)
          exact ⟨v, by simp [he, hv]⟩),
      (by intro a ha; omega)⟩, .clearRegister r)
  else if hh : s.cursor < P.R + P.M then
    let a : Fin P.M := ⟨s.cursor - P.R, by omega⟩
    (⟨s.cursor + 1, by omega, s.regs,
      (fun x => if x = a then some (zeroWord P) else s.heap x),
      (by intro r _; exact s.regs_ready r (by have := r.isLt; omega)),
      (by
        intro x hx
        by_cases he : x = a
        · exact ⟨zeroWord P, by simp [he]⟩
        · have hv : x.val ≠ s.cursor - P.R := by intro hv; apply he; exact Fin.ext hv
          obtain ⟨v, hv⟩ := s.heap_ready x (by omega)
          exact ⟨v, by simp [he, hv]⟩)⟩, .clearHeap a)
  else
    let i : Fin P.L := ⟨s.cursor - (P.R + P.M), by unfold setupUnits at h; omega⟩
    let a : Fin P.M := ⟨i.val, by have := i.isLt; have := P.layout_bound; omega⟩
    let value := boolWord P (input i)
    (⟨s.cursor + 1, by omega, s.regs,
      (fun x => if x = a then some value else s.heap x),
      (by intro r _; exact s.regs_ready r (by have := r.isLt; omega)),
      (by
        intro x _
        by_cases he : x = a
        · exact ⟨value, by simp [he]⟩
        · obtain ⟨v, hv⟩ := s.heap_ready x (by have := x.isLt; omega)
          exact ⟨v, by simp [he, hv]⟩)⟩, .copyInput i)

theorem setupStep_cursor {P : Profile} (input : Fin P.L → Bool) (s : PartialState P)
    (h : s.cursor < setupUnits P) : (setupStep input s h).1.cursor = s.cursor + 1 := by
  unfold setupStep
  split
  · rfl
  · split <;> rfl

/-- No fallback/default cell value: Option.get requires the readiness proofs. -/
def finishSetup {P : Profile} (s : PartialState P) (h : setupUnits P ≤ s.cursor) : State P where
  regs := Vector.ofFn fun r => (s.regs r).get (by
    obtain ⟨v, hv⟩ := s.regs_ready r (by have := r.isLt; unfold setupUnits at h; omega)
    simp [hv])
  heap := Vector.ofFn fun a => (s.heap a).get (by
    obtain ⟨v, hv⟩ := s.heap_ready a (by have := a.isLt; unfold setupUnits at h; omega)
    simp [hv])
  pc := zeroWord P

inductive Phase (P : Profile) where
  | setup (state : PartialState P)
  | guest (state : State P)

def normalize {P : Profile} : Phase P → Phase P
  | .setup s => if h : s.cursor < setupUnits P then .setup s
      else .guest (finishSetup s (Nat.le_of_not_gt h))
  | .guest s => .guest s

theorem normalize_setup_incomplete {P : Profile} (phase : Phase P) (s : PartialState P)
    (h : normalize phase = .setup s) : s.cursor < setupUnits P := by
  cases phase with
  | guest state => simp [normalize] at h
  | setup state =>
    by_cases hs : state.cursor < setupUnits P
    · simp only [normalize, hs, ↓reduceDIte] at h
      have he := Phase.setup.inj h
      subst s
      exact hs
    · simp [normalize, hs] at h

inductive Stop (P : Profile) where
  | halted (state : State P)
  | faulted (reason : Fault) (state : State P)
  | exhausted (phase : Phase P)

structure Result (P : Profile) where
  stop : Stop P
  trace : List (Event P)
  remaining : Nat

def prepend {P : Profile} (event : Event P) (result : Result P) : Result P :=
  { result with trace := event :: result.trace }

/-- Internal continuation helper. It is not an end-to-end cost entry point.
Normalization occurs before the zero-fuel test and emits no event. -/
def continueRun {P : Profile} (code : Program P) (input : Fin P.L → Bool) :
    Nat → Phase P → Result P
  | fuel, phase =>
    let phase := normalize phase
    match fuel with
    | 0 => ⟨.exhausted phase, [], 0⟩
    | fuel + 1 =>
      match phase with
      | .setup s =>
        if h : s.cursor < setupUnits P then
          let next := setupStep input s h
          prepend next.2 (continueRun code input fuel (.setup next.1))
        else
          -- Unreachable after normalization; still a charged actual guest step.
          let out := WordCore.step code (finishSetup s (Nat.le_of_not_gt h))
          match out.outcome with
          | .continued state => prepend (.guest out.event) (continueRun code input fuel (.guest state))
          | .halted state => ⟨.halted state, [.guest out.event], fuel⟩
          | .faulted reason state => ⟨.faulted reason state, [.guest out.event], fuel⟩
      | .guest s =>
        let out := WordCore.step code s
        match out.outcome with
        | .continued state => prepend (.guest out.event) (continueRun code input fuel (.guest state))
        | .halted state => ⟨.halted state, [.guest out.event], fuel⟩
        | .faulted reason state => ⟨.faulted reason state, [.guest out.event], fuel⟩

/-- The only fresh program entry point: all setup and execution share fuel. -/
def run (P : Profile) (code : Program P) (input : Fin P.L → Bool) (fuel : Nat) : Result P :=
  continueRun code input fuel (.setup (initialPartial P))

def Result.used {P : Profile} (result : Result P) : Nat := result.trace.length

theorem continueRun_conservation {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (phase : Phase P) :
    fuel = (continueRun code input fuel phase).used + (continueRun code input fuel phase).remaining := by
  induction fuel generalizing phase with
  | zero => rfl
  | succ fuel ih =>
    simp only [continueRun]
    cases hn : normalize phase with
    | setup s =>
      simp only
      split
      · rename_i hs
        simp only [prepend, Result.used, List.length_cons]
        have := ih (.setup (setupStep input s hs).1)
        unfold Result.used at this
        omega
      · split
        · rename_i state heq
          simp only [prepend, Result.used, List.length_cons]
          have := ih (.guest state)
          unfold Result.used at this
          omega
        · simp [Result.used, Nat.add_comm]
        · simp [Result.used, Nat.add_comm]
    | guest s =>
      simp only
      split
      · rename_i state heq
        simp only [prepend, Result.used, List.length_cons]
        have := ih (.guest state)
        unfold Result.used at this
        omega
      · simp [Result.used, Nat.add_comm]
      · simp [Result.used, Nat.add_comm]

theorem run_conservation (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) : fuel = (run P code input fuel).used + (run P code input fuel).remaining :=
  continueRun_conservation code input fuel _

def Stop.Terminal {P : Profile} : Stop P → Prop
  | .halted _ | .faulted _ _ => True
  | .exhausted _ => False

def addRemaining {P : Profile} (result : Result P) (delta : Nat) : Result P :=
  { result with remaining := result.remaining + delta }

/-- Internal continuation lemma, with no pre-existing trace or used-fuel reset. -/
theorem continueRun_terminal_mono {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (fuel delta : Nat) (phase : Phase P)
    (h : (continueRun code input fuel phase).stop.Terminal) :
    continueRun code input (fuel + delta) phase = addRemaining (continueRun code input fuel phase) delta := by
  induction fuel generalizing phase with
  | zero => simp [continueRun, Stop.Terminal] at h
  | succ fuel ih =>
    simp only [Nat.succ_add, continueRun] at h ⊢
    cases hn : normalize phase with
    | setup s =>
      have hs := normalize_setup_incomplete phase s hn
      simp only [hn, hs, ↓reduceDIte] at h ⊢
      rw [ih (.setup (setupStep input s hs).1) h]
      rfl
    | guest s =>
      simp only [hn] at h ⊢
      cases he : (WordCore.step code s).outcome with
      | continued state =>
        simp only [he] at h ⊢
        rw [ih (.guest state) h]
        rfl
      | halted state => rfl
      | faulted reason state => rfl

/-- Public terminal monotonicity always compares fresh raw-input executions. -/
theorem run_terminal_mono (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel delta : Nat) (h : (run P code input fuel).stop.Terminal) :
    run P code input (fuel + delta) = addRemaining (run P code input fuel) delta :=
  continueRun_terminal_mono code input fuel delta _ h

theorem continueRun_exhausted_remaining {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (phase finalPhase : Phase P)
    (h : (continueRun code input fuel phase).stop = .exhausted finalPhase) :
    (continueRun code input fuel phase).remaining = 0 := by
  induction fuel generalizing phase with
  | zero => rfl
  | succ fuel ih =>
    simp only [continueRun] at h ⊢
    cases hn : normalize phase with
    | setup s =>
      have hs := normalize_setup_incomplete phase s hn
      simp only [hn, hs, ↓reduceDIte] at h ⊢
      exact ih (.setup (setupStep input s hs).1) h
    | guest s =>
      simp only [hn] at h ⊢
      cases he : (WordCore.step code s).outcome with
      | continued state => simp only [he] at h ⊢; exact ih (.guest state) h
      | halted state => simp [he] at h
      | faulted reason state => simp [he] at h

theorem run_exhausted_remaining (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (phase : Phase P) (h : (run P code input fuel).stop = .exhausted phase) :
    (run P code input fuel).remaining = 0 :=
  continueRun_exhausted_remaining code input fuel _ phase h

def isRegisterClear {P : Profile} : Event P → Bool
  | .clearRegister _ => true | _ => false
def isHeapClear {P : Profile} : Event P → Bool
  | .clearHeap _ => true | _ => false
def isInputCopy {P : Profile} : Event P → Bool
  | .copyInput _ => true | _ => false
def isSetup {P : Profile} : Event P → Bool
  | .guest _ => false | _ => true
def isGuest {P : Profile} : Event P → Bool
  | .guest _ => true | _ => false
def isInvalidPC {P : Profile} : Event P → Bool
  | .guest (.invalidPC _) => true | _ => false
def isOpcode {P : Profile} (opcode : Opcode) : Event P → Bool
  | .guest (.instruction op _) => decide (op = opcode) | _ => false
def isCompletedLoad {P : Profile} : Event P → Bool
  | .guest (.instruction .load .continued) => true | _ => false
def isCompletedStore {P : Profile} : Event P → Bool
  | .guest (.instruction .store .continued) => true | _ => false

structure Ledger where
  clearRegisters : Nat
  clearHeap : Nat
  inputCopies : Nat
  invalidPCAttempts : Nat
  opcodeAttempts : Opcode → Nat
  completedLoads : Nat
  completedStores : Nat

/-- Definitionally the per-kind counts of the actual chronological trace. No
independent cost labels or guest-supplied counters are accepted. -/
def ledgerOf {P : Profile} (trace : List (Event P)) : Ledger :=
  ⟨trace.countP isRegisterClear, trace.countP isHeapClear, trace.countP isInputCopy,
    trace.countP isInvalidPC, fun op => trace.countP (isOpcode op),
    trace.countP isCompletedLoad, trace.countP isCompletedStore⟩

def Result.ledger {P : Profile} (result : Result P) : Ledger := ledgerOf result.trace
def Ledger.setupUnits (l : Ledger) : Nat := l.clearRegisters + l.clearHeap + l.inputCopies
def opcodes : List Opcode := [.const, .mov, .add, .sub, .mul, .divmod, .eq, .lt,
  .load, .store, .jump, .branch, .halt]
def Ledger.guestAttempts (l : Ledger) : Nat := l.invalidPCAttempts + (opcodes.map l.opcodeAttempts).sum
def Ledger.comparisonAttempts (l : Ledger) : Nat := l.opcodeAttempts .eq + l.opcodeAttempts .lt
def Ledger.initializedHeapWrites (l : Ledger) : Nat := l.clearHeap + l.inputCopies
def Ledger.totalCompletedHeapWrites (l : Ledger) : Nat := l.initializedHeapWrites + l.completedStores

theorem ledger_setup_projection {P : Profile} (trace : List (Event P)) :
    (ledgerOf trace).setupUnits = trace.countP isSetup := by
  induction trace with
  | nil => rfl
  | cons e rest ih =>
    cases e <;> simp_all [ledgerOf, Ledger.setupUnits, isRegisterClear, isHeapClear,
      isInputCopy, isSetup, List.countP_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem guest_event_partition {P : Profile} (e : Event P) :
    (if isInvalidPC e then 1 else 0) +
      (opcodes.map (fun op => if isOpcode op e then 1 else 0)).sum =
        (if isGuest e then 1 else 0) := by
  cases e with
  | clearRegister r => rfl
  | clearHeap a => rfl
  | copyInput i => rfl
  | guest e =>
    cases e with
    | invalidPC pc => rfl
    | instruction op disposition =>
      simp only [isInvalidPC, isGuest, isOpcode, Bool.false_eq_true,
        ↓reduceIte, Nat.zero_add, decide_eq_true_eq]
      cases op <;> decide +kernel

theorem ledger_guest_projection {P : Profile} (trace : List (Event P)) :
    (ledgerOf trace).guestAttempts = trace.countP isGuest := by
  induction trace with
  | nil => rfl
  | cons e rest ih =>
    simp only [ledgerOf, Ledger.guestAttempts, List.countP_cons] at ih ⊢
    rw [sum_map_add]
    have hp := guest_event_partition e
    omega

theorem ledger_used {P : Profile} (trace : List (Event P)) :
    trace.length = (ledgerOf trace).setupUnits + (ledgerOf trace).guestAttempts := by
  rw [ledger_setup_projection, ledger_guest_projection]
  induction trace with
  | nil => rfl
  | cons e rest ih => cases e <;> simp_all [List.countP_cons, isSetup, isGuest, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem run_ledger_conservation (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) : fuel = (run P code input fuel).ledger.setupUnits +
      (run P code input fuel).ledger.guestAttempts + (run P code input fuel).remaining := by
  have h := run_conservation P code input fuel
  simpa only [Result.used, ledger_used, Result.ledger] using h

/-- An observer, not an executed validation program. Only a halt has output. -/
def output {P : Profile} (result : Result P) : Option (Vector (Word P) P.O) :=
  match result.stop with
  | .halted s => some (Vector.ofFn fun i => s.heap.get
      ⟨P.L + i.val, by have := i.isLt; have := P.layout_bound; omega⟩)
  | _ => none

/-- Proof/specification helper for a bounded prefix of initialization actions.
It is not an alternative public cost entry point. -/
def advanceSetup {P : Profile} (input : Fin P.L → Bool) :
    (n : Nat) → (s : PartialState P) → s.cursor + n ≤ setupUnits P →
      PartialState P × List (Event P)
  | 0, s, _ => (s, [])
  | n + 1, s, h =>
      let hs : s.cursor < setupUnits P := by omega
      let next := setupStep input s hs
      let rest := advanceSetup input n next.1 (by rw [setupStep_cursor]; omega)
      (rest.1, next.2 :: rest.2)

theorem advanceSetup_cursor {P : Profile} (input : Fin P.L → Bool)
    (n : Nat) (s : PartialState P) (h : s.cursor + n ≤ setupUnits P) :
    (advanceSetup input n s h).1.cursor = s.cursor + n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [advanceSetup, ih, setupStep_cursor]; omega

theorem advanceSetup_length {P : Profile} (input : Fin P.L → Bool)
    (n : Nat) (s : PartialState P) (h : s.cursor + n ≤ setupUnits P) :
    (advanceSetup input n s h).2.length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [advanceSetup, List.length_cons, ih]

def prependTrace {P : Profile} (trace : List (Event P)) (result : Result P) : Result P :=
  { result with trace := trace ++ result.trace }

theorem continueRun_setup_prefix {P : Profile} (code : Program P) (input : Fin P.L → Bool)
    (n extra : Nat) (s : PartialState P) (h : s.cursor + n ≤ setupUnits P) :
    continueRun code input (n + extra) (.setup s) =
      prependTrace (advanceSetup input n s h).2
        (continueRun code input extra (.setup (advanceSetup input n s h).1)) := by
  induction n generalizing s with
  | zero => simp [advanceSetup, prependTrace]
  | succ n ih =>
    have hs : s.cursor < setupUnits P := by omega
    rw [Nat.succ_add, continueRun]
    simp only [normalize, hs, ↓reduceDIte]
    rw [ih (setupStep input s hs).1 (by rw [setupStep_cursor]; omega)]
    rfl

def completeSetup (P : Profile) (input : Fin P.L → Bool) : PartialState P × List (Event P) :=
  advanceSetup input (setupUnits P) (initialPartial P) (by simp [initialPartial])

theorem completeSetup_cursor (P : Profile) (input : Fin P.L → Bool) :
    (completeSetup P input).1.cursor = setupUnits P := by
  simpa [completeSetup, initialPartial] using advanceSetup_cursor input (setupUnits P) (initialPartial P)
    (by simp [initialPartial])

theorem completeSetup_length (P : Profile) (input : Fin P.L → Bool) :
    (completeSetup P input).2.length = setupUnits P :=
  advanceSetup_length input (setupUnits P) (initialPartial P) _

def setupEvent (P : Profile) (i : Fin (setupUnits P)) : Event P :=
  if hr : i.val < P.R then .clearRegister ⟨i.val, hr⟩
  else if hh : i.val < P.R + P.M then .clearHeap ⟨i.val - P.R, by omega⟩
  else .copyInput ⟨i.val - (P.R + P.M), by have := i.isLt; unfold setupUnits at this; omega⟩

theorem setupStep_event {P : Profile} (input : Fin P.L → Bool) (s : PartialState P)
    (h : s.cursor < setupUnits P) : (setupStep input s h).2 = setupEvent P ⟨s.cursor, h⟩ := by
  unfold setupStep setupEvent
  split
  · rfl
  · split <;> rfl

theorem advanceSetup_trace {P : Profile} (input : Fin P.L → Bool)
    (n : Nat) (s : PartialState P) (h : s.cursor + n ≤ setupUnits P) :
    (advanceSetup input n s h).2 =
      List.ofFn (fun i : Fin n => setupEvent P ⟨s.cursor + i.val, by have := i.isLt; omega⟩) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [advanceSetup, ih, setupStep_cursor, List.ofFn_succ]
    congr 1
    · simp only [Fin.val_zero, Nat.add_zero, setupStep_event]
    · apply congrArg List.ofFn
      funext i
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

def setupSchedule (P : Profile) : List (Event P) :=
  List.ofFn Event.clearRegister ++ List.ofFn Event.clearHeap ++ List.ofFn Event.copyInput

theorem setupEvent_schedule (P : Profile) : List.ofFn (setupEvent P) = setupSchedule P := by
  unfold setupSchedule
  change List.ofFn (fun i : Fin ((P.R + P.M) + P.L) => setupEvent P i) = _
  rw [List.ofFn_add, List.ofFn_add]
  congr 2
  · apply congrArg List.ofFn
    funext i
    simp [setupEvent, i.isLt]
  · apply congrArg List.ofFn
    funext i
    have hi := i.isLt
    simp only [setupEvent, Fin.val_castLE, Fin.val_natAdd]
    split
    · omega
    · split
      · congr 1
        apply Fin.ext
        dsimp
        omega
      · omega
  · funext i
    have hi := i.isLt
    simp only [setupEvent, Fin.val_natAdd]
    split
    · omega
    · split
      · omega
      · congr 1
        apply Fin.ext
        dsimp
        omega

theorem completeSetup_trace (P : Profile) (input : Fin P.L → Bool) :
    (completeSetup P input).2 = setupSchedule P := by
  rw [completeSetup, advanceSetup_trace]
  simpa only [initialPartial, Nat.zero_add] using setupEvent_schedule P

private theorem countP_ofFn_constant {α : Type} (n : Nat) (f : Fin n → α)
    (p : α → Bool) (b : Bool) (h : ∀ i, p (f i) = b) :
    (List.ofFn f).countP p = if b then n else 0 := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, ih (fun i => f i.succ) (by intro i; exact h i.succ)]
    rw [h 0]
    cases b <;> simp

theorem completeSetup_counts (P : Profile) (input : Fin P.L → Bool) :
    (ledgerOf (completeSetup P input).2).clearRegisters = P.R ∧
    (ledgerOf (completeSetup P input).2).clearHeap = P.M ∧
    (ledgerOf (completeSetup P input).2).inputCopies = P.L ∧
    (ledgerOf (completeSetup P input).2).guestAttempts = 0 := by
  rw [completeSetup_trace, ledger_guest_projection]
  simp only [ledgerOf, setupSchedule, List.countP_append]
  have cRR := countP_ofFn_constant P.R (@Event.clearRegister P) isRegisterClear true (by intro i; rfl)
  have cRM := countP_ofFn_constant P.M (@Event.clearHeap P) isRegisterClear false (by intro i; rfl)
  have cRL := countP_ofFn_constant P.L (@Event.copyInput P) isRegisterClear false (by intro i; rfl)
  have cMR := countP_ofFn_constant P.R (@Event.clearRegister P) isHeapClear false (by intro i; rfl)
  have cMM := countP_ofFn_constant P.M (@Event.clearHeap P) isHeapClear true (by intro i; rfl)
  have cML := countP_ofFn_constant P.L (@Event.copyInput P) isHeapClear false (by intro i; rfl)
  have cLR := countP_ofFn_constant P.R (@Event.clearRegister P) isInputCopy false (by intro i; rfl)
  have cLM := countP_ofFn_constant P.M (@Event.clearHeap P) isInputCopy false (by intro i; rfl)
  have cLL := countP_ofFn_constant P.L (@Event.copyInput P) isInputCopy true (by intro i; rfl)
  have cGR := countP_ofFn_constant P.R (@Event.clearRegister P) isGuest false (by intro i; rfl)
  have cGM := countP_ofFn_constant P.M (@Event.clearHeap P) isGuest false (by intro i; rfl)
  have cGL := countP_ofFn_constant P.L (@Event.copyInput P) isGuest false (by intro i; rfl)
  simp only [cRR, cRM, cRL, cMR, cMM, cML, cLR, cLM, cLL, cGR, cGM, cGL,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
  simp

def initialized (P : Profile) (input : Fin P.L → Bool) : State P :=
  finishSetup (completeSetup P input).1 (Nat.le_of_eq (completeSetup_cursor P input).symm)

def RegistersZero {P : Profile} (s : PartialState P) : Prop :=
  ∀ r, s.regs r = none ∨ s.regs r = some (zeroWord P)

theorem setupStep_registers_zero {P : Profile} (input : Fin P.L → Bool) (s : PartialState P)
    (h : s.cursor < setupUnits P) (hz : RegistersZero s) : RegistersZero (setupStep input s h).1 := by
  unfold setupStep
  split
  · intro r
    dsimp only
    split
    · exact Or.inr rfl
    · exact hz r
  · split <;> exact hz

theorem advanceSetup_registers_zero {P : Profile} (input : Fin P.L → Bool)
    (n : Nat) (s : PartialState P) (h : s.cursor + n ≤ setupUnits P) (hz : RegistersZero s) :
    RegistersZero (advanceSetup input n s h).1 := by
  induction n generalizing s with
  | zero => exact hz
  | succ n ih => exact ih _ _ (setupStep_registers_zero input s _ hz)

theorem initialized_registers_zero (P : Profile) (input : Fin P.L → Bool) (r : Register P) :
    (initialized P input).readReg r = zeroWord P := by
  have hz := advanceSetup_registers_zero input (setupUnits P) (initialPartial P)
    (by simp [initialPartial]) (by intro r; exact Or.inl rfl)
  change RegistersZero (completeSetup P input).1 at hz
  have hr := (completeSetup P input).1.regs_ready r
    (by rw [completeSetup_cursor]; have := r.isLt; unfold setupUnits; omega)
  obtain ⟨v, hv⟩ := hr
  have he : (completeSetup P input).1.regs r = some (zeroWord P) := by
    rcases hz r with hn | hz
    · rw [hn] at hv; contradiction
    · exact hz
  simp only [initialized, finishSetup, State.readReg, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  change ((completeSetup P input).1.regs r).get _ = zeroWord P
  simp [he]

/-- Exact logical heap contents at every setup cursor, including unwritten cells. -/
def heapAt {P : Profile} (input : Fin P.L → Bool) (cursor : Nat) (a : Fin P.M) : Option (Word P) :=
  if hc : a.val < P.L ∧ P.R + P.M + a.val < cursor then
    some (boolWord P (input ⟨a.val, hc.1⟩))
  else if P.R + a.val < cursor then some (zeroWord P) else none

def HeapContents {P : Profile} (input : Fin P.L → Bool) (s : PartialState P) : Prop :=
  ∀ a, s.heap a = heapAt input s.cursor a

theorem setupStep_heap_contents {P : Profile} (input : Fin P.L → Bool) (s : PartialState P)
    (h : s.cursor < setupUnits P) (hc : HeapContents input s) :
    HeapContents input (setupStep input s h).1 := by
  unfold setupStep
  split
  · rename_i hr
    intro a
    dsimp only
    rw [hc a]
    have h0 : ¬(a.val < P.L ∧ P.R + P.M + a.val < s.cursor) := by omega
    have h1 : ¬(a.val < P.L ∧ P.R + P.M + a.val < s.cursor + 1) := by omega
    have h2 : ¬P.R + a.val < s.cursor := by omega
    have h3 : ¬P.R + a.val < s.cursor + 1 := by omega
    simp [heapAt, h0, h1, h2, h3]
  · rename_i hr
    split
    · rename_i hm
      intro a
      dsimp only
      have h0 : ¬(a.val < P.L ∧ P.R + P.M + a.val < s.cursor) := by omega
      have h1 : ¬(a.val < P.L ∧ P.R + P.M + a.val < s.cursor + 1) := by omega
      split
      · rename_i he
        have hv := congrArg Fin.val he
        dsimp at hv
        have h2 : P.R + a.val < s.cursor + 1 := by omega
        simp [heapAt, h1, h2]
      · rename_i he
        have hv : a.val ≠ s.cursor - P.R := by intro hv; exact he (Fin.ext hv)
        have h2 : (P.R + a.val < s.cursor + 1) ↔ (P.R + a.val < s.cursor) := by omega
        rw [hc a]
        simp [heapAt, h0, h1, h2]
    · rename_i hm
      intro a
      dsimp only
      have hclear : P.R + a.val < s.cursor := by have := a.isLt; omega
      have hclear' : P.R + a.val < s.cursor + 1 := by omega
      split
      · rename_i he
        have hv := congrArg Fin.val he
        dsimp at hv
        have ha : a.val < P.L := by unfold setupUnits at h; omega
        have hcopy : a.val < P.L ∧ P.R + P.M + a.val < s.cursor + 1 := by omega
        simp only [heapAt, hcopy]
        congr 3
        exact Fin.ext hv.symm
      · rename_i he
        have hv : a.val ≠ s.cursor - (P.R + P.M) := by intro hv; exact he (Fin.ext hv)
        have heq : (a.val < P.L ∧ P.R + P.M + a.val < s.cursor + 1) ↔
            (a.val < P.L ∧ P.R + P.M + a.val < s.cursor) := by omega
        rw [hc a]
        simp only [heapAt, heq, hclear, hclear', ↓reduceIte]

theorem advanceSetup_heap_contents {P : Profile} (input : Fin P.L → Bool)
    (n : Nat) (s : PartialState P) (h : s.cursor + n ≤ setupUnits P)
    (hc : HeapContents input s) : HeapContents input (advanceSetup input n s h).1 := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih _ _ (setupStep_heap_contents input s _ hc)

theorem completeSetup_heap_contents (P : Profile) (input : Fin P.L → Bool) :
    HeapContents input (completeSetup P input).1 := by
  apply advanceSetup_heap_contents
  intro a
  simp [initialPartial, heapAt]

theorem initialized_input (P : Profile) (input : Fin P.L → Bool) (i : Fin P.L) :
    (initialized P input).heap.get ⟨i.val, by have := i.isLt; have := P.layout_bound; omega⟩ =
      boolWord P (input i) := by
  have hc := completeSetup_heap_contents P input
  let a : Fin P.M := ⟨i.val, by have := i.isLt; have := P.layout_bound; omega⟩
  have hcopy : a.val < P.L ∧ P.R + P.M + a.val < setupUnits P := by
    have := i.isLt; dsimp [a, setupUnits]; omega
  have he : (completeSetup P input).1.heap a = some (boolWord P (input i)) := by
    rw [hc a, completeSetup_cursor]
    simp [heapAt, hcopy, a]
  simp only [initialized, finishSetup, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  change ((completeSetup P input).1.heap a).get _ = _
  simp [he]

theorem initialized_rest_zero (P : Profile) (input : Fin P.L → Bool)
    (a : Fin P.M) (ha : P.L ≤ a.val) : (initialized P input).heap.get a = zeroWord P := by
  have hc := completeSetup_heap_contents P input
  have hcopy : ¬(a.val < P.L ∧ P.R + P.M + a.val < setupUnits P) := by omega
  have hclear : P.R + a.val < setupUnits P := by have := a.isLt; unfold setupUnits; omega
  have he : (completeSetup P input).1.heap a = some (zeroWord P) := by
    rw [hc a, completeSetup_cursor]
    simp [heapAt, hcopy, hclear]
  simp only [initialized, finishSetup, Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  change ((completeSetup P input).1.heap a).get _ = _
  simp [he]

/-- Exact generic setup boundary, including the shared remaining guest budget.
The prefix is the actual setup action trace, not a separately assigned cost. -/
theorem run_setup_boundary (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (extra : Nat) :
    run P code input (setupUnits P + extra) =
      prependTrace (completeSetup P input).2
        (continueRun code input extra (.guest (initialized P input))) := by
  unfold run
  rw [continueRun_setup_prefix code input (setupUnits P) extra (initialPartial P) (by simp [initialPartial])]
  change prependTrace (completeSetup P input).2
    (continueRun code input extra (.setup (completeSetup P input).1)) = _
  congr 1
  rw [continueRun.eq_def, continueRun.eq_def]
  simp only [normalize, completeSetup_cursor, Nat.lt_irrefl, ↓reduceDIte, initialized]

theorem initialized_pc_zero (P : Profile) (input : Fin P.L → Bool) :
    (initialized P input).pc = zeroWord P := rfl

/-- A strict setup prefix exhausts in its partial state: no guest is entered. -/
theorem run_before_setup (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (h : fuel < setupUnits P) :
    let setupPrefix := advanceSetup input fuel (initialPartial P) (by simp [initialPartial]; omega)
    run P code input fuel =
      { stop := .exhausted (.setup setupPrefix.1), trace := setupPrefix.2, remaining := 0 } := by
  dsimp only
  unfold run
  have hp := continueRun_setup_prefix code input fuel 0 (initialPartial P)
    (by simp [initialPartial]; omega)
  simp only [Nat.add_zero] at hp
  rw [hp]
  have ht : (advanceSetup input fuel (initialPartial P) (by simp [initialPartial]; omega)).1.cursor < setupUnits P := by
    rw [advanceSetup_cursor]
    simpa [initialPartial] using h
  simp [continueRun, normalize, ht, prependTrace]

/-- Exact budget I ends in the fully initialized guest state without a fetch. -/
theorem run_at_setup (P : Profile) (code : Program P) (input : Fin P.L → Bool) :
    run P code input (setupUnits P) =
      { stop := .exhausted (.guest (initialized P input)),
        trace := (completeSetup P input).2, remaining := 0 } := by
  simpa [continueRun, normalize, prependTrace] using run_setup_boundary P code input 0

/-- An external expected-output predicate evaluated only on a fresh raw run.
It is not a guest validation routine or a solver-correctness assertion. -/
def Produces (P : Profile) (code : Program P) (input : Fin P.L → Bool)
    (fuel : Nat) (expected : Vector (Word P) P.O) : Prop :=
  output (run P code input fuel) = some expected


/-- Finite diagnostics below are not certified output observations. -/
private def cursorDiagnostic {P : Profile} (result : Result P) : Option Nat :=
  match result.stop with
  | .exhausted (.setup s) => some s.cursor
  | _ => none

private def stateDiagnostic {P : Profile} (result : Result P) : Option (State P) :=
  match result.stop with
  | .exhausted (.guest s) | .halted s | .faulted _ s => some s
  | _ => none

private def testProfile : Profile :=
  ⟨3, 2, 4, 2, 1, by decide, by decide, by decide, by decide⟩
private instance : NeZero testProfile.bound := ⟨by decide⟩
private instance : NeZero testProfile.R := ⟨by decide⟩
private def testInput : Fin testProfile.L → Bool := fun i => i.val == 0
private def haltCode : Program testProfile := ⟨#[.halt], by decide⟩
private def emptyCode : Program testProfile := ⟨#[], by decide⟩
private def expectedState : State testProfile := ⟨#v[0, 0], #v[1, 0, 0, 0], 0⟩
private def expectedSetup : List (Event testProfile) :=
  [.clearRegister ⟨0, by decide⟩, .clearRegister ⟨1, by decide⟩,
    .clearHeap ⟨0, by decide⟩, .clearHeap ⟨1, by decide⟩,
    .clearHeap ⟨2, by decide⟩, .clearHeap ⟨3, by decide⟩,
    .copyInput ⟨0, by decide⟩, .copyInput ⟨1, by decide⟩]

theorem setup_boundary_checks :
    cursorDiagnostic (run testProfile haltCode testInput 0) = some 0 ∧
    (run testProfile haltCode testInput 0).trace = [] ∧
    cursorDiagnostic (run testProfile haltCode testInput 7) = some 7 ∧
    stateDiagnostic (run testProfile haltCode testInput 7) = none ∧
    stateDiagnostic (run testProfile haltCode testInput 8) = some expectedState ∧
    (run testProfile haltCode testInput 8).trace = expectedSetup ∧
    output (run testProfile haltCode testInput 8) = none ∧
    output (run testProfile haltCode testInput 9) = some #v[0] ∧
    (run testProfile haltCode testInput 9).trace = expectedSetup ++ [.guest (.instruction .halt .halted)] ∧
    stateDiagnostic (run testProfile emptyCode testInput 8) = some expectedState ∧
    (run testProfile emptyCode testInput 8).trace = expectedSetup ∧
    (run testProfile emptyCode testInput 9).trace = expectedSetup ++ [.guest (.invalidPC 0)] ∧
    output (run testProfile emptyCode testInput 9) = none := by
  repeat' constructor
  all_goals decide +kernel

/-- Untouched zero output can be valid for a zero expectation; a different
expectation fails. Neither exhaustion nor fault certifies even that zero output. -/
theorem expected_output_checks :
    Produces testProfile haltCode testInput 9 #v[0] ∧
    ¬Produces testProfile haltCode testInput 9 #v[1] ∧
    ¬Produces testProfile haltCode testInput 8 #v[0] ∧
    ¬Produces testProfile emptyCode testInput 9 #v[0] := by
  unfold Produces
  repeat' constructor
  all_goals decide +kernel


theorem setup_ledger_checks :
    let l := (run testProfile haltCode testInput 9).ledger
    l.clearRegisters = 2 ∧ l.clearHeap = 4 ∧ l.inputCopies = 2 ∧
    l.setupUnits = 8 ∧ l.guestAttempts = 1 ∧ l.opcodeAttempts .halt = 1 ∧
    l.initializedHeapWrites = 6 ∧ l.completedLoads = 0 ∧ l.completedStores = 0 := by
  decide +kernel

theorem access_disposition_checks :
    let trace : List (Event testProfile) :=
      [.guest (.instruction .load .continued),
       .guest (.instruction .load (.faulted .heapAddress)),
       .guest (.instruction .store .continued),
       .guest (.instruction .store (.faulted .heapAddress))]
    (ledgerOf trace).opcodeAttempts .load = 2 ∧
    (ledgerOf trace).opcodeAttempts .store = 2 ∧
    (ledgerOf trace).completedLoads = 1 ∧ (ledgerOf trace).completedStores = 1 := by
  decide +kernel

end Research.WordRun
