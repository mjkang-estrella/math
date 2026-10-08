import Research.WordQueryCode
import Research.WordRun

/-! Proposed W016 output/fresh-run predicates only, pending independent review.
No query correctness, budget sufficiency, cost comparison or new ECDLP goal is
asserted. The existing Machine/Problem/Goals and word semantics are unchanged. -/
namespace Research.WordQuerySpec

open WordCore WordQueryData WordQueryCode

/-- Both result tags are explicit; a zero payload can be a successful match.
The witness is an array location, while payload is arbitrary bounded data. -/
def ValidOutput {s : Sizes} (d : Data s) (flag payload : Nat) : Prop :=
  (flag = 1 ∧ ∃ j : Fin s.m,
    (d.entries.get j).key = d.query ∧ (d.entries.get j).payload.val = payload) ∨
  (flag = 0 ∧ payload = 0 ∧ ∀ j : Fin s.m, (d.entries.get j).key ≠ d.query)

/-- Internal result relation. Only a halted result exposes an output vector;
this helper alone is not a fresh-run correctness or resource claim. -/
def ResultValid {s : Sizes} (h : Admissible s) (d : Data s)
    (r : WordRun.Result (profile s h.1)) : Prop :=
  ∃ out, WordRun.output r = some out ∧
    ValidOutput d (out.get ⟨0, by decide⟩).val (out.get ⟨1, by decide⟩).val

/-- Fresh entry only, using the admitted profile, actual raw encoding and the
unchanged common budget. Host expected tables/states are not runner arguments. -/
def CorrectOn {s : Sizes} (h : Admissible s) (code : Program (profile s h.1))
    (d : Data s) : Prop :=
  ResultValid h d (WordRun.run (profile s h.1) code (rawInput d) s.F)

/-- Every sorted bounded table and every bounded query at one admitted public
shape. Code is fixed before the data quantifier. This is a target, not a theorem. -/
def SolvesAt (s : Sizes) (h : Admissible s) (code : Program (profile s h.1)) : Prop :=
  ∀ d : Data s, Sorted d → CorrectOn h code d

/-- The two prescribed size-only constructors, on their common admitted domain.
No existential choice of input-specialized code or fuel is available here. -/
def BothSolve : Prop :=
  ∀ s : Sizes, ∀ h : Admissible s, SolvesAt s h (linear s h) ∧ SolvesAt s h (binary s h)

theorem validOutput_tag {s : Sizes} (d : Data s) (flag payload : Nat)
    (h : ValidOutput d flag payload) : flag = 0 ∨ flag = 1 := by
  rcases h with h | h
  · exact Or.inr h.1
  · exact Or.inl h.1

theorem resultValid_halted {s : Sizes} (h : Admissible s) (d : Data s)
    (r : WordRun.Result (profile s h.1)) (hr : ResultValid h d r) :
    ∃ st, r.stop = .halted st := by
  obtain ⟨out, ho, _⟩ := hr
  cases he : r.stop with
  | halted st => exact ⟨st, rfl⟩
  | faulted reason st => simp [WordRun.output, he] at ho
  | exhausted phase => simp [WordRun.output, he] at ho

end Research.WordQuerySpec
