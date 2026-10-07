import Research.Problem

namespace Research

/-- Fixed-instance resource target. Program size limits tables in the finite
control, but does not constrain advice in public parameters or the encoding.
Reviewed inputs and separate hardware calibration are required; abstract tape
steps are not GPU curve operations. -/
def ConcreteGoal (P : CyclicProblem) (maxProgramBits maxSteps : Nat) : Prop :=
  ∃ code : Machine.Program,
    Machine.descriptionBits code ≤ maxProgramBits ∧
    SolvesWithin P code maxSteps

/-- A family with n-bit-scale group orders, without hardness constraints. Coordinates, parameter
encodings, and their uniform efficient generation still require external
review and formal refinement before this is an ECDLP benchmark. -/
structure ProblemFamily where
  problem : Nat → CyclicProblem
  order_lower : ∀ n, 2 ^ n ≤ (problem n).order
  order_upper : ∀ n, (problem n).order < 2 ^ (n + 1)

/-- Strong illustrative breakthrough target:
  one fixed program, correct on every scalar at every size, and eventually
  T(n)^(2k) ≤ C * q(n)^(k-1), for some k≥1 and C≥1.
Equivalently T = O(q^(1/2 - 1/(2k))) over positive real quantities.
This avoids floating-point exponents and is stronger than merely o(sqrt q).
This is a GOAL DEFINITION, not a claimed theorem or a discovered solver. -/
def ExponentBreakthrough (F : ProblemFamily) : Prop :=
  ∃ code : Machine.Program, ∃ budget : Nat → Nat,
    (∀ n, SolvesWithin (F.problem n) code (budget n)) ∧
    ∃ k C N : Nat, 0 < k ∧ 0 < C ∧
      ∀ n, N ≤ n → (budget n) ^ (2 * k) ≤ C * (F.problem n).order ^ (k - 1)

/-- Paper estimates remain explicit assumptions. This statement does not say
that actual cryptanalytic work or physical GPU throughput equals these values. -/
def EnoughCapacity (work rate workers seconds : Nat) : Prop :=
  work ≤ rate * workers * seconds

theorem million_gpu_week_below_reference :
    ¬ EnoughCapacity (2 ^ 128) 19300000000 1000000 604800 := by
  unfold EnoughCapacity
  decide +kernel

theorem even_10_quadrillion_speedup_below_reference :
    19300000000 * 1000000 * 604800 * 10000000000000000 < 2 ^ 128 := by
  decide +kernel

end Research
