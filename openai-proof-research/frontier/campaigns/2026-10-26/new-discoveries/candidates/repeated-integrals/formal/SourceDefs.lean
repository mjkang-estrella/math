import MomentDefs

open Set
open scoped ContDiff

namespace RepeatedIntegrals

def SourceW (n : ℕ) : Set (MomentSpace n) :=
  {b | ∃ f : ℝ → ℝ,
    ContDiffOn ℝ n f (Icc (0 : ℝ) 1) ∧
    MonotoneOn (iteratedDerivWithin n f (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) ∧
    (¬ ∃ c : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin n f (Icc (0 : ℝ) 1) t = c) ∧
    (∀ j ≤ n, iteratedDerivWithin j f (Icc (0 : ℝ) 1) 0 = 0) ∧
    (∀ j : Fin (n + 1), iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) 1 = b j)}

def GoodWitness (n : ℕ) (b : MomentSpace n) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧
  (∀ j ≤ n, iteratedDeriv j f 0 = 0) ∧
  (∀ j : Fin (n + 1), iteratedDeriv j.val f 1 = b j) ∧
  (∀ t ∈ Ioo (0 : ℝ) 1, 0 < iteratedDeriv (n + 1) f t) ∧
  iteratedDeriv (n + 1) f 0 = 1 ∧
  iteratedDeriv (n + 1) f 1 = 1 ∧
  (∀ j : ℕ, n + 1 < j → iteratedDeriv j f 0 = 0 ∧ iteratedDeriv j f 1 = 0)

def SourceConjecture371768 : Prop :=
  ∀ n : ℕ, IsOpen (SourceW n) ∧ ∀ b ∈ SourceW n, ∃ f, GoodWitness n b f

end RepeatedIntegrals
