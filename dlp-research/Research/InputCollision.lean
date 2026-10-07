import Research.Checks

/-!
A negative specification test: injective finite bit lists need not give
distinct initial machine tapes. This example leaves all core definitions
unchanged and demonstrates a missing input-representation obligation.
-/
namespace Research.InputCollision

/-- Two distinct point encodings: the empty list and one zero bit. -/
def problem : CyclicProblem :=
  { Checks.toy with
    encodePoint := fun (b : Bool) => if b then [false] else []
    encode_injective := by
      intro a b h
      cases a <;> cases b <;> simp_all <;> rfl }

theorem encoded_inputs_distinct :
    problem.input ⟨0, by decide⟩ ≠ problem.input ⟨1, by decide⟩ := by
  decide +kernel

/-- Both lists initialize exactly the same record, not just equivalent tapes. -/
theorem initial_tapes_equal :
    Machine.Tape.ofBits (problem.input ⟨0, by decide⟩) =
      Machine.Tape.ofBits (problem.input ⟨1, by decide⟩) := by
  rfl

theorem executions_equal (code : Machine.Program) (fuel : Nat) :
    Machine.execute code fuel (problem.input ⟨0, by decide⟩) =
      Machine.execute code fuel (problem.input ⟨1, by decide⟩) := by
  rfl

/-- No deterministic program can recover both scalars from this representation,
even though it is a valid inhabitant of the current cyclic problem interface. -/
theorem no_solver (code : Machine.Program) (fuel : Nat) :
    ¬ SolvesWithin problem code fuel := by
  intro h
  obtain ⟨out0, hrun0, hbits0⟩ := h ⟨0, by decide⟩
  obtain ⟨out1, hrun1, hbits1⟩ := h ⟨1, by decide⟩
  rw [← executions_equal code fuel, hrun0] at hrun1
  have hout : out0 = out1 := Option.some.inj hrun1
  rw [← hout, hbits0] at hbits1
  have : bits 1 0 = bits 1 1 := hbits1
  simp [bits] at this

end Research.InputCollision
