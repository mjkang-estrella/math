import Research.Problem
import Research.SmallCurve

/-! An algebra refinement on the existing cyclic orbit only.
The refinement laws are proof obligations supplied by concrete implementations,
not global axioms. No comparator, table lookup, RAM, tape, or hardware cost
semantics is introduced here. Points outside the orbit receive no guarantees.
-/
namespace Research.OrbitRefinement

def orbit (P : CyclicProblem) (n : Nat) : P.Point := iteratePoint P.next P.zero n

theorem iterate_add {Point : Type} (next : Point → Point) (zero : Point) (a b : Nat) :
    iteratePoint next zero (a + b) = iteratePoint next (iteratePoint next zero a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change next (iteratePoint next zero (a + b)) =
      next (iteratePoint next (iteratePoint next zero a) b)
    exact congrArg next ih

theorem orbit_period (P : CyclicProblem) (n : Nat) : orbit P (n + P.order) = orbit P n := by
  unfold orbit
  rw [Nat.add_comm n P.order, iterate_add, P.wraps]

theorem orbit_add_mul_order (P : CyclicProblem) (n k : Nat) :
    orbit P (n + P.order * k) = orbit P n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, orbit_period, ih]

theorem orbit_mod (P : CyclicProblem) (n : Nat) : orbit P n = orbit P (n % P.order) := by
  calc
    orbit P n = orbit P (n % P.order + P.order * (n / P.order)) :=
      congrArg (orbit P) (Nat.mod_add_div n P.order).symm
    _ = orbit P (n % P.order) := orbit_add_mul_order P _ _

theorem orbit_eq_iff_mod (P : CyclicProblem) (a b : Nat) :
    orbit P a = orbit P b ↔ a % P.order = b % P.order := by
  constructor
  · intro h
    rw [orbit_mod P a, orbit_mod P b] at h
    have hf := P.distinct
      ⟨a % P.order, Nat.mod_lt _ P.order_pos⟩
      ⟨b % P.order, Nat.mod_lt _ P.order_pos⟩ h
    exact congrArg Fin.val hf
  · intro h
    rw [orbit_mod P a, orbit_mod P b, h]

theorem publicKey_orbit (P : CyclicProblem) (d : Fin P.order) :
    P.publicKey d = orbit P d.val := rfl

theorem order_one_orbit (P : CyclicProblem) (h : P.order = 1) (n : Nat) :
    orbit P n = P.zero := by
  rw [orbit_mod P n, h, Nat.mod_one]
  rfl

/-- Executable operations with laws restricted to points on the cyclic orbit.
No efficiency claim follows from these fields. -/
structure OrbitArithmetic (P : CyclicProblem) where
  add : P.Point → P.Point → P.Point
  neg : P.Point → P.Point
  add_orbit : ∀ a b, add (orbit P a) (orbit P b) = orbit P (a + b)
  neg_orbit : ∀ a, neg (orbit P a) = orbit P ((P.order - a % P.order) % P.order)

theorem add_generator (P : CyclicProblem) (A : OrbitArithmetic P) (n : Nat) :
    A.add (orbit P n) (orbit P 1) = P.next (orbit P n) := by
  rw [A.add_orbit]
  rfl

theorem add_publicKeys (P : CyclicProblem) (A : OrbitArithmetic P)
    (a b : Fin P.order) :
    A.add (P.publicKey a) (P.publicKey b) = orbit P (a.val + b.val) :=
  A.add_orbit _ _

theorem neg_publicKey (P : CyclicProblem) (A : OrbitArithmetic P) (a : Fin P.order) :
    A.neg (P.publicKey a) = orbit P ((P.order - a.val) % P.order) := by
  change A.neg (orbit P a.val) = _
  simpa only [Nat.mod_eq_of_lt a.isLt] using A.neg_orbit a.val

theorem smallCurve_add_orbit (a b : Nat) :
    SmallCurve.add (orbit SmallCurve.problem a) (orbit SmallCurve.problem b) =
      orbit SmallCurve.problem (a + b) := by
  change SmallCurve.add (SmallCurve.multiple a) (SmallCurve.multiple b) =
    SmallCurve.multiple (a + b)
  induction b with
  | zero => exact SmallCurve.add_infinity _
  | succ b ih =>
    change SmallCurve.add (SmallCurve.multiple a)
      (SmallCurve.add (SmallCurve.multiple b) SmallCurve.generator) =
      SmallCurve.add (SmallCurve.multiple (a + b)) SmallCurve.generator
    rw [← SmallCurve.add_assoc, ih]

private theorem smallCurve_neg_finite : ∀ a : Fin 7,
    SmallCurve.neg (SmallCurve.multiple a.val) =
      SmallCurve.multiple ((7 - a.val) % 7) := by
  decide +kernel

theorem smallCurve_neg_orbit (a : Nat) :
    SmallCurve.neg (orbit SmallCurve.problem a) =
      orbit SmallCurve.problem ((SmallCurve.problem.order - a % SmallCurve.problem.order) %
        SmallCurve.problem.order) := by
  rw [orbit_mod SmallCurve.problem a]
  exact smallCurve_neg_finite ⟨a % 7, Nat.mod_lt _ (by decide)⟩

/-- This instance uses the existing coordinate formulas, not inverse-log search. -/
def smallCurve : OrbitArithmetic SmallCurve.problem where
  add := SmallCurve.add
  neg := SmallCurve.neg
  add_orbit := smallCurve_add_orbit
  neg_orbit := smallCurve_neg_orbit

/-- One instrumented invocation of the concrete addition function.
The returned unit counts only this call, not its internal arithmetic. -/
def countedAdd (P : CyclicProblem) (A : OrbitArithmetic P) (p q : P.Point) :
    P.Point × Nat := (A.add p q, 1)

structure Babies (P : CyclicProblem) where
  entries : List (P.Point × Nat)
  final : P.Point
  countedAddCalls : Nat

/-- Forward construction with one `countedAdd` wrapper invocation per recursive step. Entries
carry their forward indices. The helper's correctness is stated only when its
starting point is on the orbit. Its count includes only the direct `A.add` call
inside each wrapper. Evaluating `orbit P 1` may itself invoke `P.next` and
coordinate additions; these generator computations are excluded. Consing, scalar
arithmetic, allocation, encoding, comparisons, and all interpreter/tape costs
are also excluded. This is not a count of all coordinate-add executions. -/
def buildFrom (P : CyclicProblem) (A : OrbitArithmetic P) (current : P.Point)
    (start : Nat) : Nat → Babies P
  | 0 => ⟨[], current, 0⟩
  | m + 1 =>
      let step := countedAdd P A current (orbit P 1)
      let rest := buildFrom P A step.1 (start + 1) m
      ⟨(current, start) :: rest.entries, rest.final, step.2 + rest.countedAddCalls⟩

def buildBabies (P : CyclicProblem) (A : OrbitArithmetic P) (m : Nat) : Babies P :=
  buildFrom P A P.zero 0 m

theorem buildFrom_length (P : CyclicProblem) (A : OrbitArithmetic P)
    (current : P.Point) (start m : Nat) :
    (buildFrom P A current start m).entries.length = m := by
  induction m generalizing current start with
  | zero => rfl
  | succ m ih => simp only [buildFrom, List.length_cons, ih]

theorem buildFrom_countedAddCalls (P : CyclicProblem) (A : OrbitArithmetic P)
    (current : P.Point) (start m : Nat) :
    (buildFrom P A current start m).countedAddCalls = m := by
  induction m generalizing current start with
  | zero => rfl
  | succ m ih => simp only [buildFrom, countedAdd, ih]; omega

theorem buildFrom_final (P : CyclicProblem) (A : OrbitArithmetic P) (k m : Nat) :
    (buildFrom P A (orbit P k) k m).final = orbit P (k + m) := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    simp only [buildFrom, countedAdd, A.add_orbit]
    rw [ih]
    congr 1
    omega

theorem buildFrom_entry (P : CyclicProblem) (A : OrbitArithmetic P) (k m j : Nat)
    (h : j < m) :
    (buildFrom P A (orbit P k) k m).entries[j]? = some (orbit P (k + j), k + j) := by
  induction m generalizing k j with
  | zero => omega
  | succ m ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [buildFrom, countedAdd, A.add_orbit, List.getElem?_cons_succ]
      rw [ih (k + 1) j (by omega)]
      rw [show k + 1 + j = k + (j + 1) by omega]

theorem buildBabies_length (P : CyclicProblem) (A : OrbitArithmetic P) (m : Nat) :
    (buildBabies P A m).entries.length = m := buildFrom_length P A P.zero 0 m

theorem buildBabies_countedAddCalls (P : CyclicProblem) (A : OrbitArithmetic P) (m : Nat) :
    (buildBabies P A m).countedAddCalls = m := buildFrom_countedAddCalls P A P.zero 0 m

theorem buildBabies_final (P : CyclicProblem) (A : OrbitArithmetic P) (m : Nat) :
    (buildBabies P A m).final = orbit P m := by
  simpa only [buildBabies, orbit, iteratePoint, Nat.zero_add] using buildFrom_final P A 0 m

theorem buildBabies_entry (P : CyclicProblem) (A : OrbitArithmetic P) (m j : Nat)
    (h : j < m) :
    (buildBabies P A m).entries[j]? = some (orbit P j, j) := by
  simpa only [buildBabies, orbit, iteratePoint, Nat.zero_add] using buildFrom_entry P A 0 m j h

/-- Specializations include empty, unit, exact-order, and wrapped construction.
The general theorems above apply at every natural m, not just these cases. -/
theorem smallCurve_baby_edges : ∀ m : Fin 9,
    (buildBabies SmallCurve.problem smallCurve m.val).entries.length = m.val ∧
      (buildBabies SmallCurve.problem smallCurve m.val).countedAddCalls = m.val ∧
      (buildBabies SmallCurve.problem smallCurve m.val).final =
        SmallCurve.multiple (m.val % 7) := by
  intro m
  refine ⟨buildBabies_length SmallCurve.problem smallCurve m.val,
    buildBabies_countedAddCalls SmallCurve.problem smallCurve m.val, ?_⟩
  change (buildBabies SmallCurve.problem smallCurve m.val).final =
    orbit SmallCurve.problem (m.val % 7)
  exact (buildBabies_final SmallCurve.problem smallCurve m.val).trans
    (orbit_mod SmallCurve.problem m.val)

end Research.OrbitRefinement
