import Research.Machine

namespace Research

/-- Little-endian fixed-width binary representation. -/
def bits (width value : Nat) : List Bool :=
  match width with
  | 0 => []
  | w + 1 => (value % 2 == 1) :: bits w (value / 2)

def iteratePoint {Point : Type} (next : Point → Point) (zero : Point) : Nat → Point
  | 0 => zero
  | n + 1 => next (iteratePoint next zero n)

/-- A cyclic-orbit discrete-log interface. For an elliptic curve, `next` must
be proved to be addition by G and `zero` must be the point at infinity.
Constructing this interface is not itself an elliptic-curve formalization. -/
structure CyclicProblem where
  Point : Type
  order : Nat
  order_pos : 0 < order
  zero : Point
  next : Point → Point
  wraps : iteratePoint next zero order = zero
  distinct : ∀ a b : Fin order,
    iteratePoint next zero a.val = iteratePoint next zero b.val → a = b
  encodePoint : Point → List Bool
  encode_injective : ∀ a b, encodePoint a = encodePoint b → a = b
  /-- Fixed public parameters; never a per-secret advice string. -/
  parameters : List Bool
  outputWidth : Nat
  fits : order ≤ 2 ^ outputWidth

def CyclicProblem.publicKey (P : CyclicProblem) (d : Fin P.order) : P.Point :=
  iteratePoint P.next P.zero d.val

def CyclicProblem.input (P : CyclicProblem) (d : Fin P.order) : List Bool :=
  P.parameters ++ P.encodePoint (P.publicKey d)

/-- Deterministic, all-input correctness AND a worst-case machine-step bound.
The only input to the program is the encoded public instance and public key. -/
def SolvesWithin (P : CyclicProblem) (code : Machine.Program) (steps : Nat) : Prop :=
  ∀ d : Fin P.order, ∃ out,
    Machine.execute code steps (P.input d) = some out ∧
    out.read P.outputWidth = bits P.outputWidth d.val

end Research
