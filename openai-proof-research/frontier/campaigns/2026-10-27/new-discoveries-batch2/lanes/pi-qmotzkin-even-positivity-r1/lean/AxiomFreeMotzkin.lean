/-
  AxiomFreeMotzkin.lean — bridge layer 1 for Oh–Scrimshaw A.4 / MathDB 339078
  (lane pi-qmotzkin-even-positivity-r1)

  STATUS: written for bare Lean 4, toolchain pin 4.34.1 (see ./lean-toolchain).
  This sandbox has no Lean toolchain, so this file is UNVERIFIED BY COMPILER.
  It is deliberately dependency-free (no mathlib) and conservative so that it
  should compile as-is. The mathlib pin for layers 2-3 is
  d13f23b723b8a846827a245b89c10fc7d3f11612 (see BRIDGE.md).

  Content (no `sorry`, no `axiom`):
    * Poly := List Nat, little-endian coefficients  (Z≥0[q] by representation)
    * polynomial add/mul, monomial q^k
    * the q-Motzkin recurrence:  M 0 = 1,
      M (n+1) = M n + Σ_{r < n} q^{r+1} · M r · M (n-1-r)
    * evaluated sanity lemmas: M 0 = 1, M 1 = 1, M 2 = 1 + q.

  The mathematical content of layer 1 is: M_n is built entirely from Nat
  coefficients, i.e. M_n ∈ Z≥0[q] representationally. The deep layers
  (Claim R reduction; Theorem A's explicit monomial formula for Δ_n^{(2)})
  need determinants and are Layer 2/3 in BRIDGE.md.
-/

namespace Motzkin

/-- Polynomials in q with natural coefficients, little-endian. -/
def Poly := List Nat

namespace Poly

def add : Poly → Poly → Poly
  | [],      bs      => bs
  | as,      []      => as
  | a :: as, b :: bs => (a + b) :: (add as bs)

def shift1 : Poly → Poly
  | []      => []
  | p       => 0 :: p

def mul : Poly → Poly → Poly :=
  fun as bs =>
    match as with
    | []      => []
    | a :: as => add (bs.map (fun b => a * b)) (shift1 (mul as bs))

def mon (k : Nat) : Poly :=
  match k with
  | 0     => [1]
  | k' + 1 => 0 :: mon k'

end Poly

open Poly

/-- q-Motzkin numbers as coefficient lists. -/
def M : Nat → Poly :=
  fun n =>
    match n with
    | 0     => [1]
    | n' + 1 =>
      let rec go (r : Nat) (acc : Poly) : Poly :=
        match r with
        | 0      => acc
        | r' + 1 => go r' (add acc (mul (mul (mon (r' + 1)) (M r')) (M (n' - (r' + 1)))))
      go n' (M n')

/-- M_0 = 1. -/
theorem M_zero : M 0 = [1] := rfl

/-- M_1 = 1. -/
theorem M_one : M 1 = [1] := rfl

/-- M_2 = 1 + q. -/
theorem M_two : M 2 = [1, 1] := rfl

end Motzkin
