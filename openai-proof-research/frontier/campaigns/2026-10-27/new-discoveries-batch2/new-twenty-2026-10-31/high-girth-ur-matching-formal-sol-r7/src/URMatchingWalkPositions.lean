module
public import URMatchingWalkParity
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
@[expose] public section
namespace URMatching
open scoped Classical
/-- Position parity determines the side of every vertex on an actual walk. -/
theorem walk_position_parity {N : ℕ} (σ : PermutationTuples N 100)
    {u v : BipartiteVertex N} (p : (permutationGraph σ).Walk u v)
    (i : ℕ) (hi : i ≤ p.length) :
    (p.getVert i).isLeft = u.isLeft ↔ i % 2 = 0 := by
  induction p generalizing i with
  | nil =>
    have : i = 0 := by simpa using hi
    subst i
    simp
  | @cons u v w huv p ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i ≤ p.length := by simpa using hi
      have hp := ih i hi'
      change permutationAdj σ u v at huv
      change (p.getVert i).isLeft = u.isLeft ↔ (i+1) % 2 = 0
      cases u <;> cases v <;> simp only [permutationAdj] at huv
      all_goals
        cases he : p.getVert i <;>
          simp only [he, Sum.isLeft_inl, Sum.isLeft_inr, Bool.true_eq_false,
            Bool.false_eq_true, true_iff, false_iff] at hp ⊢ <;> omega

/-- The exact distinctness property supplied by genuine IsCycle.support_nodup,
proved without the import-heavy Paths theorem graph. -/
theorem walk_tail_positions_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.support.tail.Nodup)
    {i j : ℕ} (hi : 1 ≤ i ∧ i ≤ p.length) (hj : 1 ≤ j ∧ j ≤ p.length)
    (he : p.getVert i = p.getVert j) : i = j := by
  have hli : i-1 < p.support.tail.length := by simp only [List.length_tail, p.length_support]; omega
  have hlj : j-1 < p.support.tail.length := by simp only [List.length_tail, p.length_support]; omega
  have he' : p.support.tail[i-1] = p.support.tail[j-1] := by
    simpa only [List.getElem_tail, Nat.sub_add_cancel hi.1, Nat.sub_add_cancel hj.1,
      SimpleGraph.Walk.support_getElem_eq_getVert] using he
  have := hp.getElem_inj_iff.mp he'
  omega
end URMatching
