import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
namespace UnitCoset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def Admissible (A B : Finset G) (f : A ≃ B) : Prop :=
  ∀ a : A, (a : G) + (f a : G) ∉ A

def sumMap {A B : Finset G} (f : A ≃ B) (a : A) : G :=
  (a : G) + (f a : G)

def multiplicity {A B : Finset G} (f : A ≃ B) (x : G) : ℕ :=
  (Finset.univ.filter fun a : A => sumMap f a = x).card

def support {A B : Finset G} (f : A ≃ B) : Finset G :=
  Finset.univ.image (sumMap f)

-- One entry per support point, with repetitions of equal positive fibre sizes.
def sequence {A B : Finset G} (f : A ≃ B) : List ℕ :=
  ((support f).val.map (multiplicity f)).sort (· ≥ ·)

def UnitSequence {A B : Finset G} (f : A ≃ B) : Prop :=
  ∀ n ∈ sequence f, n = 1

def Acyclic {A B : Finset G} (f : A ≃ B) : Prop :=
  ∀ g : A ≃ B, Admissible A B g → multiplicity g = multiplicity f → g = f

def Standing (A B : Finset G) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ A.card = B.card ∧ 0 ∉ B ∧
    ∀ a ∈ A, ∀ b ∈ B, a + b ∉ A

def Conjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [DecidableEq G] (A B : Finset G),
    Standing A B → ∃ f : A ≃ B, Admissible A B f ∧ UnitSequence f ∧ Acyclic f
end UnitCoset
