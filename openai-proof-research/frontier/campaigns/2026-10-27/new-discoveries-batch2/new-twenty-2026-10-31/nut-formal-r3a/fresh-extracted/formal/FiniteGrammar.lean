import VerifiedDet
import Mathlib.Data.Fintype.Powerset
namespace Nut8
abbrev QuotientMatrix := Matrix (Fin 8) (Fin 8) ℤ
/-- Cut formulation of connected support, using only a bounded finite domain. -/
def SupportConnected (C : QuotientMatrix) : Prop :=
  ∀ S : Finset (Fin 8), S.Nonempty → S ≠ Finset.univ →
    ∃ i ∈ S, ∃ j ∉ S, C i j ≠ 0

/-- Coherent contribution grammar. Opposite double-edge signs have already been excluded.
A diagonal magnitude two is one loop; a magnitude one is one semi-edge. -/
def Admissible (C : QuotientMatrix) (ε s : ℤ) : Prop :=
  (ε = 1 ∨ ε = -1) ∧ (s = 1 ∨ s = -1) ∧
  (∀ i j, C i j = C j i) ∧
  (∀ i, ∑ j, |C i j| = 3) ∧
  (∀ i j, |C i j| ≤ 2) ∧
  (∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = -2 ∨ C i i = s) ∧
  (ε = 1 → ∀ i j, 0 ≤ C i j) ∧ SupportConnected C

instance (C : QuotientMatrix) (ε s : ℤ) : Decidable (Admissible C ε s) := by
  unfold Admissible SupportConnected
  dsimp [QuotientMatrix, Matrix] at C ⊢
  infer_instance

def unsignedQuotient (C : QuotientMatrix) : QuotientMatrix := fun i j => |C i j|

lemma unsigned_row_sum (C : QuotientMatrix) (ε s : ℤ) (h : Admissible C ε s)
    (i : Fin 8) : ∑ j, unsignedQuotient C i j = 3 := h.2.2.2.1 i

lemma trivial_character_unsigned (C : QuotientMatrix) (s : ℤ) (h : Admissible C 1 s) :
    unsignedQuotient C = C := by
  funext i j
  exact abs_of_nonneg (h.2.2.2.2.2.2.1 rfl i j)

/-- Explicit proposed finite endpoint; no inhabitant is claimed in this module. -/
def FiniteObstruction : Prop := ∀ C ε s, Admissible C ε s →
  ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)
end Nut8
