module
public import URMatchingSurvivorGraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
@[expose] public section
namespace URMatching
open scoped Classical
/-- Every walk in the actual permutation graph alternates between its two sides. -/
theorem permutation_walk_parity {N : ℕ} (σ : PermutationTuples N 100)
    {u v : BipartiteVertex N} (p : (permutationGraph σ).Walk u v) :
    p.length % 2 = 0 ↔ u.isLeft = v.isLeft := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    change (p.length + 1) % 2 = 0 ↔ u.isLeft = w.isLeft
    change permutationAdj σ u v at huv
    cases u <;> cases v <;> cases w <;>
      simp_all only [permutationAdj, Sum.isLeft_inl, Sum.isLeft_inr, Bool.true_eq_false,
        Bool.false_eq_true, iff_false, iff_true] <;> omega
/-- In particular genuine cycles, and even arbitrary closed walks, have even length. -/
theorem permutation_closed_walk_even {N : ℕ} (σ : PermutationTuples N 100)
    {u : BipartiteVertex N} (p : (permutationGraph σ).Walk u u) :
    p.length % 2 = 0 := (permutation_walk_parity σ p).mpr rfl
end URMatching
