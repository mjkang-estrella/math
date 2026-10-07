import Std

/-!
A small deterministic binary-tape machine. Cost is the number of executed
non-halting transitions, not a number supplied by the candidate algorithm.
Finite-control lookup counts as part of one abstract machine transition.
This is a mathematical cost model, not a GPU timing model.
-/
namespace Research.Machine

structure Tape where
  left : List Bool := []
  head : Bool := false
  right : List Bool := []
  deriving Repr, DecidableEq

def Tape.ofBits (bits : List Bool) : Tape :=
  match bits with
  | [] => {}
  | b :: bs => { head := b, right := bs }

def Tape.moveRight (t : Tape) : Tape :=
  match t.right with
  | [] => { left := t.head :: t.left }
  | b :: bs => { left := t.head :: t.left, head := b, right := bs }

def Tape.moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] => { right := t.head :: t.right }
  | b :: bs => { left := bs, head := b, right := t.head :: t.right }

def Tape.read (t : Tape) : Nat → List Bool
  | 0 => []
  | n + 1 => t.head :: t.moveRight.read n

inductive Instruction where
  | halt
  | write (bit : Bool) (next : Nat)
  | left (next : Nat)
  | right (next : Nat)
  | branch (ifFalse ifTrue : Nat)
  deriving Repr, DecidableEq

abbrev Program := List Instruction

structure Config where
  pc : Nat := 0
  tape : Tape
  deriving Repr, DecidableEq

def step (code : Program) (c : Config) : Option Config := do
  match ← code[c.pc]? with
  | .halt => none
  | .write bit next => some { pc := next, tape := { c.tape with head := bit } }
  | .left next => some { pc := next, tape := c.tape.moveLeft }
  | .right next => some { pc := next, tape := c.tape.moveRight }
  | .branch f t => some { c with pc := if c.tape.head then t else f }

/-- `some` means an explicit halt was reached within the budget.
An invalid program counter or exhausted fuel returns `none`.
Reaching a halt instruction takes no additional transition. -/
def run (code : Program) : Nat → Config → Option Tape
  | fuel, c =>
    if code[c.pc]? == some .halt then some c.tape
    else match fuel with
      | 0 => none
      | k + 1 => (step code c).bind (run code k)

def execute (code : Program) (fuel : Nat) (input : List Bool) : Option Tape :=
  run code fuel { tape := Tape.ofBits input }

/-- Includes bit lengths of control-flow addresses; large tables cannot be
hidden in a single instruction for the concrete program-size goal. -/
def Instruction.descriptionBits : Instruction → Nat
  | .halt => 3
  | .write _ n => 4 + 2 * (n + 1).log2 + 1
  | .left n | .right n => 3 + 2 * (n + 1).log2 + 1
  | .branch f t => 3 + (2 * (f + 1).log2 + 1) + (2 * (t + 1).log2 + 1)

def descriptionBits (code : Program) : Nat :=
  (code.map Instruction.descriptionBits).sum

theorem run_mono (code : Program) (fuel : Nat) (c : Config) (out : Tape)
    (h : run code fuel c = some out) : run code (fuel + 1) c = some out := by
  induction fuel generalizing c with
  | zero =>
    simp only [run] at h ⊢
    split at h <;> simp_all
  | succ fuel ih =>
    simp only [run] at h ⊢
    split at h
    · simp_all
    · rename_i hn
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      cases hs : step code c with
      | none => simp [hs] at h
      | some next =>
        simp only [hs, Option.bind_some] at h ⊢
        exact ih next h

end Research.Machine
