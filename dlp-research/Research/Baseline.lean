import Research.Problem

/-!
Exhaustive cyclic-orbit search with an instrumented equality-test count.
This is a high-level reference baseline, not a binary-tape implementation.
Its count excludes point addition, equality internals, allocation and bit costs.
-/
namespace Research.Baseline

structure Result where
  scalar : Option Nat
  comparisons : Nat
  deriving Repr, DecidableEq

/-- Traverse from the supplied point, testing before taking the next step.
No inverse table is supplied or constructed. -/
def scan {Point : Type} [DecidableEq Point] (next : Point → Point)
    (target : Point) : Nat → Nat → Point → Result
  | 0, _, _ => ⟨none, 0⟩
  | fuel + 1, offset, point =>
    if point = target then ⟨some offset, 1⟩
    else
      let rest := scan next target fuel (offset + 1) (next point)
      ⟨rest.scalar, rest.comparisons + 1⟩

theorem scan_comparisons_le {Point : Type} [DecidableEq Point]
    (next : Point → Point) (target : Point) (fuel offset : Nat) (point : Point) :
    (scan next target fuel offset point).comparisons ≤ fuel := by
  induction fuel generalizing offset point with
  | zero => simp [scan]
  | succ fuel ih =>
    simp only [scan]
    split
    · simp
    · exact Nat.add_le_add_right (ih (offset + 1) (next point)) 1

theorem scan_orbit (P : CyclicProblem) [DecidableEq P.Point]
    (d : Fin P.order) (fuel offset : Nat)
    (hle : offset ≤ d.val) (hroom : d.val < offset + fuel) :
    scan P.next (P.publicKey d) fuel offset
      (iteratePoint P.next P.zero offset) =
      ⟨some d.val, d.val - offset + 1⟩ := by
  induction fuel generalizing offset with
  | zero => omega
  | succ fuel ih =>
    by_cases heq : offset = d.val
    · subst offset
      simp [scan, CyclicProblem.publicKey]
    · have hoff : offset < P.order := by have := d.isLt; omega
      have hne : iteratePoint P.next P.zero offset ≠ P.publicKey d := by
        intro h
        have hf := P.distinct ⟨offset, hoff⟩ d h
        have := congrArg Fin.val hf
        exact heq this
      simp only [scan, hne, ↓reduceIte]
      have hrec := ih (offset + 1) (by omega) (by omega)
      change scan P.next (P.publicKey d) fuel (offset + 1)
        (P.next (iteratePoint P.next P.zero offset)) = _ at hrec
      rw [hrec]
      simp only
      congr 1
      omega

def solve (P : CyclicProblem) [DecidableEq P.Point] (target : P.Point) : Result :=
  scan P.next target P.order 0 P.zero

/-- Every secret is recovered; the literal loop performs exactly d+1 tests. -/
theorem solve_publicKey (P : CyclicProblem) [DecidableEq P.Point]
    (d : Fin P.order) : solve P (P.publicKey d) = ⟨some d.val, d.val + 1⟩ := by
  simpa [solve, iteratePoint] using
    scan_orbit P d P.order 0 (by omega) (by have := d.isLt; omega)

theorem solve_comparisons_le (P : CyclicProblem) [DecidableEq P.Point]
    (target : P.Point) : (solve P target).comparisons ≤ P.order := by
  exact scan_comparisons_le P.next target P.order 0 P.zero

end Research.Baseline
