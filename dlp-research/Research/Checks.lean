import Research.Goals
import Research.Secp256k1
import Research.SmallCurve
import Research.Baseline

namespace Research.Checks

local instance : DecidableEq SmallCurve.problem.Point :=
  inferInstanceAs (DecidableEq SmallCurve.Point)

/-- All seven secrets on the coordinate curve are recovered by the high-level
reference scan. The count measures equality tests, not tape transitions. -/
theorem small_curve_baseline (d : Fin SmallCurve.problem.order) :
    Baseline.solve SmallCurve.problem (SmallCurve.problem.publicKey d) =
      ⟨some d.val, d.val + 1⟩ := by
  exact Baseline.solve_publicKey SmallCurve.problem d

theorem small_curve_baseline_worst_case :
    Baseline.solve SmallCurve.problem (SmallCurve.problem.publicKey ⟨6, by decide⟩) =
      ⟨some 6, 7⟩ := by
  decide +kernel

/-- Deliberately trivial group of order two: validates the framework only.
It carries no evidence about large elliptic curves. -/
def toy : CyclicProblem where
  Point := Bool
  order := 2
  order_pos := by decide
  zero := false
  next := Bool.not
  wraps := by rfl
  distinct := by
    intro a b h
    have ha : a.val = 0 ∨ a.val = 1 := by omega
    have hb : b.val = 0 ∨ b.val = 1 := by omega
    apply Fin.ext
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · omega
    · simp [ha, hb, iteratePoint] at h
    · simp [ha, hb, iteratePoint] at h
    · omega
  encodePoint := fun b => [b]
  encode_injective := by intro a b h; simpa using h
  parameters := []
  outputWidth := 1
  fits := by decide

theorem toy_solved : SolvesWithin toy [.halt] 0 := by
  intro d
  have hd : d.val = 0 ∨ d.val = 1 := by have := d.isLt; change d.val < 2 at this; omega
  refine ⟨Machine.Tape.ofBits (toy.input d), ?_, ?_⟩
  · rfl
  · rcases hd with hd | hd <;>
      simp [CyclicProblem.input, CyclicProblem.publicKey, toy, hd,
        iteratePoint, Machine.Tape.ofBits, Machine.Tape.read, bits]

theorem toy_goal : ConcreteGoal toy 3 0 := by
  exact ⟨[.halt], by decide, toy_solved⟩

theorem empty_code_rejected : Machine.execute [] 10 [true] = none := by
  decide +kernel

theorem infinite_branch_exhausts :
    Machine.execute [.branch 0 0] 20 [true] = none := by
  decide +kernel

theorem write_needs_fuel :
    Machine.execute [.write true 1, .halt] 0 [false] = none := by
  decide +kernel

theorem write_succeeds :
    (Machine.execute [.write true 1, .halt] 1 [false]).map (fun t => t.read 1) =
      some [true] := by
  decide +kernel

theorem move_left_then_right :
    (Machine.execute [.left 1, .right 2, .halt] 2 [true, false]).map
      (fun t => t.read 2) = some [true, false] := by
  decide +kernel

end Research.Checks
