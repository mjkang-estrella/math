module
public import URMatchingSurvivorGap
public import Mathlib.Data.Nat.Cast.Order.Ring
@[expose] public section
namespace URMatching
open scoped Classical
variable {K : Type*} [Semiring K] [LinearOrder K] [IsStrictOrderedRing K]
theorem survivor_strict_gap_cast {a h : ℕ} (σ : PermutationTuples (4*a) 100)
    (hd : 100 * (removedVertices (4*a) h σ).card < 4*a)
    (hn : SurvivorNoHole h a σ) :
    (4 : K) * (urMatchingNumber (survivorGraph h σ) : K) <
      3 * (matchingNumber (survivorGraph h σ) : K) := by
  have hg := survivor_strict_gap σ hd hn
  exact_mod_cast hg
end URMatching
