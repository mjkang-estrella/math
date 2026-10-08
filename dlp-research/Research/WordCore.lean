import Std

/-!
W011 internal guest-step component only. No initialization, raw-input runner,
fuel, ledger, serialization, query code, or end-to-end program cost is supplied.
All events below are determined by the actual fetch and instruction outcome.
Array/vector access and checked natural arithmetic implement the separately
reviewed abstract word semantics; they carry no hardware or bit-cost claim.
-/
namespace Research.WordCore

structure Profile where
  W : Nat
  R : Nat
  M : Nat
  L : Nat
  O : Nat
  W_pos : 0 < W
  R_pos : 0 < R
  heap_bound : M ≤ 2 ^ W
  layout_bound : L + O ≤ M
  deriving Repr, DecidableEq

def Profile.bound (P : Profile) : Nat := 2 ^ P.W
abbrev Word (P : Profile) := Fin P.bound
abbrev Register (P : Profile) := Fin P.R

inductive Instr (P : Profile) where
  | const (d : Register P) (v t : Word P)
  | mov (d a : Register P) (t : Word P)
  | add (d a b : Register P) (t : Word P)
  | sub (d a b : Register P) (t : Word P)
  | mul (d a b : Register P) (t : Word P)
  | divmod (dq dr a b : Register P) (t : Word P)
  | eq (d a b : Register P) (t : Word P)
  | lt (d a b : Register P) (t : Word P)
  | load (d a : Register P) (t : Word P)
  | store (a b : Register P) (t : Word P)
  | jump (t : Word P)
  | branch (a : Register P) (t0 t1 : Word P)
  | halt
  deriving Repr, DecidableEq

structure Program (P : Profile) where
  code : Array (Instr P)
  bounded : code.size ≤ P.bound
  deriving Repr, DecidableEq

structure State (P : Profile) where
  regs : Vector (Word P) P.R
  heap : Vector (Word P) P.M
  pc : Word P
  deriving Repr, DecidableEq

inductive Opcode where
  | const | mov | add | sub | mul | divmod | eq | lt | load | store | jump | branch | halt
  deriving Repr, DecidableEq

def Instr.opcode {P : Profile} : Instr P → Opcode
  | .const .. => .const
  | .mov .. => .mov
  | .add .. => .add
  | .sub .. => .sub
  | .mul .. => .mul
  | .divmod .. => .divmod
  | .eq .. => .eq
  | .lt .. => .lt
  | .load .. => .load
  | .store .. => .store
  | .jump .. => .jump
  | .branch .. => .branch
  | .halt => .halt

inductive Fault where
  | invalidPC | addOverflow | subUnderflow | mulOverflow | divisionByZero | heapAddress
  deriving Repr, DecidableEq

inductive Disposition where
  | continued | halted | faulted (reason : Fault)
  deriving Repr, DecidableEq

inductive Event (P : Profile) where
  | invalidPC (pc : Word P)
  | instruction (opcode : Opcode) (disposition : Disposition)
  deriving Repr, DecidableEq

inductive Outcome (P : Profile) where
  | continued (state : State P)
  | halted (state : State P)
  | faulted (reason : Fault) (state : State P)
  deriving Repr, DecidableEq

def Outcome.state {P : Profile} : Outcome P → State P
  | .continued s | .halted s | .faulted _ s => s

def Outcome.disposition {P : Profile} : Outcome P → Disposition
  | .continued _ => .continued
  | .halted _ => .halted
  | .faulted reason _ => .faulted reason

structure StepResult (P : Profile) where
  outcome : Outcome P
  event : Event P
  deriving Repr, DecidableEq

def State.readReg {P : Profile} (s : State P) (r : Register P) : Word P :=
  s.regs.get r

def State.writeReg {P : Profile} (s : State P) (r : Register P) (v : Word P) : State P :=
  { s with regs := s.regs.set r.val v r.isLt }

def boolWord (P : Profile) (b : Bool) : Word P :=
  if b then ⟨1, Nat.one_lt_two_pow (Nat.ne_of_gt P.W_pos)⟩
  else ⟨0, Nat.two_pow_pos P.W⟩

/-- Conditional internal instruction semantics. All sources are read from `s`;
division writes quotient then remainder, so an aliased destination retains the
remainder. Successor targets are not fetched or checked here. -/
def execInstr {P : Profile} (i : Instr P) (s : State P) : Outcome P :=
  match i with
  | .const d v t => .continued { s.writeReg d v with pc := t }
  | .mov d a t => .continued { s.writeReg d (s.readReg a) with pc := t }
  | .add d a b t =>
    let x := (s.readReg a).val + (s.readReg b).val
    if h : x < P.bound then .continued { s.writeReg d ⟨x, h⟩ with pc := t }
    else .faulted .addOverflow s
  | .sub d a b t =>
    if _h : (s.readReg b).val ≤ (s.readReg a).val then
      let x := (s.readReg a).val - (s.readReg b).val
      let hx : x < P.bound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s.readReg a).isLt
      .continued { s.writeReg d ⟨x, hx⟩ with pc := t }
    else .faulted .subUnderflow s
  | .mul d a b t =>
    let x := (s.readReg a).val * (s.readReg b).val
    if h : x < P.bound then .continued { s.writeReg d ⟨x, h⟩ with pc := t }
    else .faulted .mulOverflow s
  | .divmod dq dr a b t =>
    let x := (s.readReg a).val
    let y := (s.readReg b).val
    if h : y ≠ 0 then
      let q : Word P := ⟨x / y, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.readReg a).isLt⟩
      let r : Word P := ⟨x % y, Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) (s.readReg b).isLt⟩
      .continued { (s.writeReg dq q).writeReg dr r with pc := t }
    else .faulted .divisionByZero s
  | .eq d a b t =>
    .continued { s.writeReg d (boolWord P (decide (s.readReg a = s.readReg b))) with pc := t }
  | .lt d a b t =>
    .continued { s.writeReg d (boolWord P (decide ((s.readReg a).val < (s.readReg b).val))) with pc := t }
  | .load d a t =>
    let addr := (s.readReg a).val
    if h : addr < P.M then
      .continued { s.writeReg d (s.heap.get ⟨addr, h⟩) with pc := t }
    else .faulted .heapAddress s
  | .store a b t =>
    let addr := (s.readReg a).val
    let value := s.readReg b
    if h : addr < P.M then
      .continued { s with heap := s.heap.set addr value h, pc := t }
    else .faulted .heapAddress s
  | .jump t => .continued { s with pc := t }
  | .branch a t0 t1 => .continued { s with pc := if (s.readReg a).val = 0 then t0 else t1 }
  | .halt => .halted s

/-- Internal one-attempt guest step, without fuel. A future fresh runner must
check shared remaining fuel before calling it and derive its ledger from these
actual events. Invalid-PC attempts never receive an invented opcode event. -/
def step {P : Profile} (c : Program P) (s : State P) : StepResult P :=
  if h : s.pc.val < c.code.size then
    let i := c.code[s.pc.val]
    let outcome := execInstr i s
    { outcome, event := .instruction i.opcode outcome.disposition }
  else
    { outcome := .faulted .invalidPC s, event := .invalidPC s.pc }

theorem execInstr_fault_atomic {P : Profile} (i : Instr P) (s s' : State P)
    (reason : Fault) (h : execInstr i s = .faulted reason s') : s' = s := by
  cases i <;> simp only [execInstr] at h
  all_goals first | contradiction | (split at h <;> simp_all)

theorem step_invalidPC {P : Profile} (c : Program P) (s : State P)
    (h : ¬ s.pc.val < c.code.size) :
    step c s = ⟨.faulted .invalidPC s, .invalidPC s.pc⟩ := by
  simp [step, h]

theorem step_fetched {P : Profile} (c : Program P) (s : State P)
    (h : s.pc.val < c.code.size) :
    step c s = ⟨execInstr c.code[s.pc.val] s,
      .instruction c.code[s.pc.val].opcode (execInstr c.code[s.pc.val] s).disposition⟩ := by
  simp [step, h]

theorem step_fault_atomic {P : Profile} (c : Program P) (s s' : State P)
    (reason : Fault) (h : (step c s).outcome = .faulted reason s') : s' = s := by
  unfold step at h
  split at h
  · exact execInstr_fault_atomic _ _ _ _ h
  · simp_all

theorem step_opcode_correspondence {P : Profile} (c : Program P) (s : State P)
    (h : s.pc.val < c.code.size) :
    (step c s).event = .instruction c.code[s.pc.val].opcode (step c s).outcome.disposition := by
  simp [step, h]

theorem state_word_bounds {P : Profile} (s : State P) :
    s.pc.val < P.bound ∧
      (∀ r : Register P, (s.readReg r).val < P.bound) ∧
      (∀ a : Fin P.M, (s.heap.get a).val < P.bound) := by
  exact ⟨s.pc.isLt, fun r => (s.readReg r).isLt, fun a => (s.heap.get a).isLt⟩

theorem step_word_bounds {P : Profile} (c : Program P) (s : State P) :
    (step c s).outcome.state.pc.val < P.bound ∧
      (∀ r : Register P, ((step c s).outcome.state.readReg r).val < P.bound) ∧
      (∀ a : Fin P.M, ((step c s).outcome.state.heap.get a).val < P.bound) :=
  state_word_bounds (step c s).outcome.state

theorem execInstr_ne_invalidPC {P : Profile} (i : Instr P) (s s' : State P) :
    execInstr i s ≠ .faulted .invalidPC s' := by
  cases i <;> simp only [execInstr]
  all_goals first | (solve | simp) | (split <;> simp)

theorem execInstr_halted_iff {P : Profile} (i : Instr P) (s s' : State P) :
    execInstr i s = .halted s' ↔ i = .halt ∧ s = s' := by
  cases i <;> simp only [execInstr]
  all_goals first | (solve | simp) | (split <;> simp)

theorem step_invalidPC_event_iff {P : Profile} (c : Program P) (s : State P)
    (pc : Word P) :
    (step c s).event = .invalidPC pc ↔ ¬ s.pc.val < c.code.size ∧ s.pc = pc := by
  simp only [step]
  split <;> simp_all

theorem step_invalidPC_fault_iff {P : Profile} (c : Program P) (s s' : State P) :
    (step c s).outcome = .faulted .invalidPC s' ↔
      ¬ s.pc.val < c.code.size ∧ s = s' := by
  simp only [step]
  split
  · simp_all [execInstr_ne_invalidPC]
  · simp_all

/-- Generic shared-destination rule, with the remainder computed from the
original operands even when the destination also aliases an input register. -/
theorem divmod_shared_destination {P : Profile} (s : State P)
    (d a b : Register P) (t : Word P) (h : (s.readReg b).val ≠ 0) :
    execInstr (.divmod d d a b t) s =
      .continued { s.writeReg d
        ⟨(s.readReg a).val % (s.readReg b).val,
          Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) (s.readReg b).isLt⟩ with pc := t } := by
  simp [execInstr, h, State.writeReg]

/-! Tiny hand-built states below test the INTERNAL step component. These are
not initialized program runs and establish no setup, fuel, or program costs. -/
private def testProfile : Profile :=
  ⟨3, 3, 3, 0, 0, by decide, by decide, by decide, by decide⟩

private instance : NeZero testProfile.bound := ⟨by decide⟩
private instance : NeZero testProfile.R := ⟨by decide⟩

private def testState : State testProfile :=
  ⟨#v[7, 3, 0], #v[0, 0, 0], 0⟩

private def oneInstr (i : Instr testProfile) : Program testProfile :=
  ⟨#[i], by change 1 ≤ 8; decide⟩

theorem divmod_alias_checks :
    step (oneInstr (.divmod 0 1 0 1 0)) testState =
      ⟨.continued ⟨#v[2, 1, 0], #v[0, 0, 0], 0⟩, .instruction .divmod .continued⟩ ∧
    step (oneInstr (.divmod 0 0 0 1 0)) testState =
      ⟨.continued ⟨#v[1, 3, 0], #v[0, 0, 0], 0⟩, .instruction .divmod .continued⟩ ∧
    step (oneInstr (.divmod 1 0 0 1 0)) testState =
      ⟨.continued ⟨#v[1, 2, 0], #v[0, 0, 0], 0⟩, .instruction .divmod .continued⟩ := by
  decide +kernel

theorem division_zero_alias_check :
    let s : State testProfile := ⟨#v[7, 0, 0], #v[0, 0, 0], 0⟩
    step (oneInstr (.divmod 0 1 0 1 7)) s =
      ⟨.faulted .divisionByZero s, .instruction .divmod (.faulted .divisionByZero)⟩ := by
  decide +kernel

/-- The arithmetic fault occurs before any attempt to fetch its invalid target. -/
theorem arithmetic_invalid_successor_checks :
    step (oneInstr (.add 2 0 1 7)) testState =
      ⟨.faulted .addOverflow testState, .instruction .add (.faulted .addOverflow)⟩ ∧
    step (oneInstr (.sub 2 1 0 7)) testState =
      ⟨.faulted .subUnderflow testState, .instruction .sub (.faulted .subUnderflow)⟩ ∧
    step (oneInstr (.mul 2 0 1 7)) testState =
      ⟨.faulted .mulOverflow testState, .instruction .mul (.faulted .mulOverflow)⟩ := by
  decide +kernel

/-- Store commits before transfer; the later invalid fetch preserves the store. -/
theorem store_then_invalid_fetch_check :
    let c := oneInstr (.store 2 1 7)
    let stored : State testProfile := ⟨#v[7, 3, 0], #v[3, 0, 0], 7⟩
    step c testState = ⟨.continued stored, .instruction .store .continued⟩ ∧
    step c stored = ⟨.faulted .invalidPC stored, .invalidPC 7⟩ := by
  decide +kernel

theorem load_store_alias_checks :
    let s : State testProfile := ⟨#v[1, 3, 1], #v[0, 7, 0], 0⟩
    step (oneInstr (.load 0 0 0)) s =
      ⟨.continued ⟨#v[7, 3, 1], #v[0, 7, 0], 0⟩, .instruction .load .continued⟩ ∧
    step (oneInstr (.store 2 2 0)) s =
      ⟨.continued ⟨#v[1, 3, 1], #v[0, 1, 0], 0⟩, .instruction .store .continued⟩ := by
  decide +kernel

theorem heap_boundary_checks :
    let valid : State testProfile := ⟨#v[2, 7, 0], #v[0, 0, 3], 0⟩
    let invalid : State testProfile := ⟨#v[3, 7, 0], #v[0, 0, 3], 0⟩
    step (oneInstr (.load 0 0 0)) valid =
      ⟨.continued ⟨#v[3, 7, 0], #v[0, 0, 3], 0⟩, .instruction .load .continued⟩ ∧
    step (oneInstr (.load 0 0 7)) invalid =
      ⟨.faulted .heapAddress invalid, .instruction .load (.faulted .heapAddress)⟩ ∧
    step (oneInstr (.store 0 1 7)) invalid =
      ⟨.faulted .heapAddress invalid, .instruction .store (.faulted .heapAddress)⟩ := by
  decide +kernel

private def bitProfile : Profile :=
  ⟨1, 2, 0, 0, 0, by decide, by decide, by decide, by decide⟩

private instance : NeZero bitProfile.bound := ⟨by decide⟩
private instance : NeZero bitProfile.R := ⟨by decide⟩

private def bitState : State bitProfile := ⟨#v[1, 0], #v[], 0⟩

private def bitInstr (i : Instr bitProfile) : Program bitProfile := ⟨#[i], by change 1 ≤ 2; decide⟩

theorem one_bit_checks :
    step (bitInstr (.eq 0 0 1 1)) bitState =
      ⟨.continued ⟨#v[0, 0], #v[], 1⟩, .instruction .eq .continued⟩ ∧
    step (bitInstr (.lt 1 1 0 1)) bitState =
      ⟨.continued ⟨#v[1, 1], #v[], 1⟩, .instruction .lt .continued⟩ ∧
    step (bitInstr (.add 1 0 1 1)) bitState =
      ⟨.continued ⟨#v[1, 1], #v[], 1⟩, .instruction .add .continued⟩ ∧
    step (bitInstr (.add 1 0 0 1)) bitState =
      ⟨.faulted .addOverflow bitState, .instruction .add (.faulted .addOverflow)⟩ ∧
    step (bitInstr (.sub 0 1 0 1)) bitState =
      ⟨.faulted .subUnderflow bitState, .instruction .sub (.faulted .subUnderflow)⟩ ∧
    step (bitInstr (.load 1 1 1)) bitState =
      ⟨.faulted .heapAddress bitState, .instruction .load (.faulted .heapAddress)⟩ := by
  decide +kernel

private def fullProfile : Profile :=
  ⟨1, 2, 2, 0, 0, by decide, by decide, by decide, by decide⟩

private instance : NeZero fullProfile.bound := ⟨by decide⟩
private instance : NeZero fullProfile.R := ⟨by decide⟩

theorem full_capacity_last_address_check :
    let s : State fullProfile := ⟨#v[1, 0], #v[0, 1], 0⟩
    let c : Program fullProfile := ⟨#[.load 1 0 0], by decide⟩
    step c s = ⟨.continued ⟨#v[1, 1], #v[0, 1], 0⟩, .instruction .load .continued⟩ := by
  decide +kernel

theorem control_fetch_checks :
    let c := oneInstr .halt
    let invalid : State testProfile := { testState with pc := 7 }
    let empty : Program testProfile := ⟨#[], by decide⟩
    step c testState = ⟨.halted testState, .instruction .halt .halted⟩ ∧
    step c invalid = ⟨.faulted .invalidPC invalid, .invalidPC 7⟩ ∧
    step empty testState = ⟨.faulted .invalidPC testState, .invalidPC 0⟩ ∧
    step (oneInstr (.jump 7)) testState =
      ⟨.continued { testState with pc := 7 }, .instruction .jump .continued⟩ ∧
    step (oneInstr (.branch 2 7 0)) testState =
      ⟨.continued { testState with pc := 7 }, .instruction .branch .continued⟩ ∧
    step (oneInstr (.branch 1 7 0)) testState =
      ⟨.continued testState, .instruction .branch .continued⟩ := by
  decide +kernel

theorem const_mov_checks :
    step (oneInstr (.const 0 1 7)) testState =
      ⟨.continued ⟨#v[1, 3, 0], #v[0, 0, 0], 7⟩, .instruction .const .continued⟩ ∧
    step (oneInstr (.mov 0 1 7)) testState =
      ⟨.continued ⟨#v[3, 3, 0], #v[0, 0, 0], 7⟩, .instruction .mov .continued⟩ ∧
    step (oneInstr (.mov 1 1 7)) testState =
      ⟨.continued { testState with pc := 7 }, .instruction .mov .continued⟩ := by
  decide +kernel

theorem arithmetic_word_boundary_checks :
    let s : State testProfile := ⟨#v[7, 1, 0], #v[0, 0, 0], 0⟩
    let doubled : State testProfile := ⟨#v[7, 2, 0], #v[0, 0, 0], 0⟩
    step (oneInstr (.add 2 0 2 0)) s =
      ⟨.continued ⟨#v[7, 1, 7], #v[0, 0, 0], 0⟩, .instruction .add .continued⟩ ∧
    step (oneInstr (.add 2 0 1 7)) s =
      ⟨.faulted .addOverflow s, .instruction .add (.faulted .addOverflow)⟩ ∧
    step (oneInstr (.sub 2 2 2 0)) s =
      ⟨.continued s, .instruction .sub .continued⟩ ∧
    step (oneInstr (.sub 2 2 1 7)) s =
      ⟨.faulted .subUnderflow s, .instruction .sub (.faulted .subUnderflow)⟩ ∧
    step (oneInstr (.mul 2 0 1 0)) s =
      ⟨.continued ⟨#v[7, 1, 7], #v[0, 0, 0], 0⟩, .instruction .mul .continued⟩ ∧
    step (oneInstr (.mul 2 0 1 7)) doubled =
      ⟨.faulted .mulOverflow doubled, .instruction .mul (.faulted .mulOverflow)⟩ ∧
    step (oneInstr (.divmod 2 1 0 1 0)) s =
      ⟨.continued ⟨#v[7, 0, 7], #v[0, 0, 0], 0⟩, .instruction .divmod .continued⟩ ∧
    step (oneInstr (.divmod 2 1 0 0 0)) s =
      ⟨.continued ⟨#v[7, 0, 1], #v[0, 0, 0], 0⟩, .instruction .divmod .continued⟩ ∧
    step (oneInstr (.eq 2 0 0 0)) s =
      ⟨.continued ⟨#v[7, 1, 1], #v[0, 0, 0], 0⟩, .instruction .eq .continued⟩ ∧
    step (oneInstr (.lt 1 0 0 0)) s =
      ⟨.continued ⟨#v[7, 0, 0], #v[0, 0, 0], 0⟩, .instruction .lt .continued⟩ := by
  decide +kernel

end Research.WordCore
