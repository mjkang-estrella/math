import Invariances
import GraphChecker
import GraphClosure7_000
namespace Nut8

/-- The off-diagonal support of `C` is exactly the catalogue graph `code`
(row-major bit encoding on 8 vertices, as decoded by `graphBit`). -/
def SupportCode (C : QuotientMatrix) (code : Nat) : Prop :=
  ∀ i j : Fin 8, i ≠ j → (C i j ≠ 0 ↔ graphBit 8 code i.val j.val = true)

/-- Every structural quotient matrix relabels onto a catalogue support. -/
def Coverage8 : Prop :=
  ∀ (C : QuotientMatrix) (s : ℤ), Structural C s →
    ∃ (e : Equiv.Perm (Fin 8)) (code : Nat),
      code ∈ GraphClosure7_000.targets ∧ SupportCode (C.submatrix e e) code

/-- No structural matrix supported on a catalogue graph has a full one-dimensional kernel. -/
def PerSupport : Prop :=
  ∀ code ∈ GraphClosure7_000.targets, ∀ (C : QuotientMatrix) (s : ℤ),
    Structural C s → SupportCode C code →
      ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)

end Nut8
