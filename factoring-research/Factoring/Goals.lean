import Factoring.Contract

namespace Factoring

/-- An interface for a future fixed machine semantics. No implementation is supplied.
`Code` must be finite programs in a reviewed, uniform classical model. `run` must
parse binary input and count actual machine steps. Arbitrary function/cost pairs
do not establish classical complexity. See docs/SPECIFICATION.md. -/
structure MachineModel where
  Code : Type
  run : Code → Nat → Nat → Option Nat

/-- The one code is outside all input quantifiers. Fuel is polynomial in bit length.
This is a relative specification, not an assertion that such a program exists. -/
def DeterministicPolySplitter (M : MachineModel) : Prop :=
  ∃ code : M.Code, ∃ C k : Nat, 0 < C ∧
    ∀ n, Composite n → ∃ d,
      M.run code n (C * (inputBits n) ^ k) = some d ∧ NontrivialFactor n d

/-- A finite random-tape interface. Tape length, machine time, and generation of
random bits must all have the bounds required by the reviewed implementation. -/
structure RandomMachineModel where
  Code : Type
  run : Code → Nat → List Bool → Nat → Option Nat

def randomTapes : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (randomTapes k).map (false :: ·) ++ (randomTapes k).map (true :: ·)

def succeeds (M : RandomMachineModel) (code : M.Code) (n fuel : Nat)
    (tape : List Bool) : Bool :=
  match M.run code n tape fuel with
  | none => false
  | some d => accepts n d

/-- At least 2/3 of all equally likely tapes succeed on EVERY composite input.
Random bits and fuel are bounded by the same polynomial (padding is allowed).
This does not formalize an expected-time / Las Vegas guarantee. -/
def RandomizedPolySplitter (M : RandomMachineModel) : Prop :=
  ∃ code : M.Code, ∃ C k : Nat, 0 < C ∧
    ∀ n, Composite n →
      let budget := C * (inputBits n) ^ k
      let tapes := randomTapes budget
      2 * tapes.length ≤ 3 * (tapes.filter (succeeds M code n budget)).length

end Factoring

