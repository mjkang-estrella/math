import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Lattice.Nat
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace JohnsonRefutation
abbrev Vertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}
def Adj {n k : ℕ} (u v : Vertex n k) : Prop := (u.val ∩ v.val).card = k-1
instance {n k : ℕ} (u v : Vertex n k) : Decidable (Adj u v) := inferInstanceAs (Decidable ((u.val ∩ v.val).card = k-1))
structure PathDecomposition {V : Type} [Fintype V] (adj : V → V → Prop) (m : ℕ) where
 bag : Fin m → Finset V
 cover : ∀ v, ∃ i, v ∈ bag i
 edge : ∀ u v, adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
 interval : ∀ (i j l : Fin m) v, i ≤ j → j ≤ l → v ∈ bag i → v ∈ bag l → v ∈ bag j
noncomputable def pathwidth {V : Type} [Fintype V] (adj : V → V → Prop) : ℕ :=
 sInf {w | ∃ (m : ℕ) (P : PathDecomposition adj m), ∀ i, (P.bag i).card ≤ w+1}
theorem pathwidth_le {V : Type} [Fintype V] {adj : V → V → Prop} {m w : ℕ}
 (P : PathDecomposition adj m) (h : ∀ i, (P.bag i).card ≤ w+1) : pathwidth adj ≤ w := by
 apply Nat.sInf_le
 exact ⟨m, P, h⟩
def code (v : Vertex 8 4) : ℕ := ∑ i ∈ v.val, 2^i.val
def starts : Array ℕ := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,1,0,0,0,57,0,6,49,0,0,0,0,0,0,0,0,30,0,0,0,66,0,18,44,0,0,0,0,23,0,25,9,0,0,2,36,0,12,0,0,0,0,0,0,0,0,0,0,13,0,0,0,58,0,7,37,0,0,0,0,39,0,11,41,0,0,35,38,0,28,0,0,0,0,0,0,5,0,0,21,0,0,31,24,0,14,0,0,0,0,3,27,0,29,0,0,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,56,0,0,0,69,0,64,59,0,0,0,0,55,0,17,53,0,0,61,60,0,48,0,0,0,0,0,0,68,0,19,51,0,0,67,65,0,46,0,0,0,0,16,42,0,15,0,0,0,43,0,0,0,0,0,0,0,0,0,0,52,0,4,50,0,0,63,62,0,47,0,0,0,0,32,40,0,26,0,0,0,22,0,0,0,0,0,0,0,0,20,45,0,8,0,0,0,10,0,0,0,0,0,0,0,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def ends : Array ℕ := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,69,0,0,0,0,0,0,0,57,0,0,0,69,0,64,60,0,0,0,0,0,0,0,0,68,0,0,0,69,0,67,66,0,0,0,0,68,0,30,53,0,0,67,66,0,49,0,0,0,0,0,0,0,0,0,0,58,0,0,0,69,0,64,62,0,0,0,0,58,0,41,53,0,0,63,62,0,49,0,0,0,0,0,0,68,0,31,51,0,0,67,66,0,47,0,0,0,0,39,45,0,41,0,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,69,0,0,0,69,0,69,69,0,0,0,0,69,0,64,60,0,0,69,69,0,64,0,0,0,0,0,0,69,0,68,68,0,0,69,69,0,67,0,0,0,0,68,68,0,53,0,0,0,67,0,0,0,0,0,0,0,0,0,0,69,0,64,62,0,0,69,69,0,64,0,0,0,0,63,62,0,53,0,0,0,63,0,0,0,0,0,0,0,0,68,68,0,51,0,0,0,67,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def first (v : Vertex 8 4) : ℕ := starts[code v]!
def last (v : Vertex 8 4) : ℕ := ends[code v]!
def bags (i : Fin 70) : Finset (Vertex 8 4) := Finset.univ.filter (fun v => first v ≤ i.val ∧ i.val ≤ last v)
theorem interval_bounds : ∀ v : Vertex 8 4, first v ≤ last v ∧ last v < 70 := by decide
theorem edge_bounds : ∀ u v : Vertex 8 4, Adj u v → first u ≤ last v ∧ first v ≤ last u := by decide
theorem bag_card : ∀ i : Fin 70, (bags i).card ≤ 41 := by decide
noncomputable def decomposition : PathDecomposition (@Adj 8 4) 70 where
 bag := bags
 cover := by
  intro v
  refine ⟨⟨first v, lt_of_le_of_lt (interval_bounds v).1 (interval_bounds v).2⟩, ?_⟩
  simp only [bags, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨le_rfl, (interval_bounds v).1⟩
 edge := by
  intro u v h
  let t := max (first u) (first v)
  have ht : t < 70 := max_lt (lt_of_le_of_lt (interval_bounds u).1 (interval_bounds u).2)
    (lt_of_le_of_lt (interval_bounds v).1 (interval_bounds v).2)
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · simp only [bags, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_max_left _ _, max_le (interval_bounds u).1 (edge_bounds u v h).2⟩
  · simp only [bags, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_max_right _ _, max_le (edge_bounds u v h).1 (interval_bounds v).1⟩
 interval := by
  intro i j l v hij hjl hi hl
  simp only [bags, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact ⟨le_trans hi.1 hij, le_trans hjl hl.2⟩
theorem johnson_pathwidth_le_40 : pathwidth (@Adj 8 4) ≤ 40 :=
 pathwidth_le decomposition bag_card
def summand (n k t : ℕ) : ℕ :=
 t * (n-t).choose (k-1) + t * (∑ i ∈ Finset.Icc 2 k, ((k-i)*t).choose (k-i)) -
 (∑ i ∈ Finset.Icc 1 (k-1), ((k-i-1)*t+1).choose (k-i))
def sourceBound (n k : ℕ) : ℕ := max (summand n k ((n+1)/k)) (summand n k ((n+k-1)/k)) - 1
theorem source_bound_8_4 : sourceBound 8 4 = 43 := by decide
def SourcePathwidthClaim : Prop := ∀ n k : ℕ, 2 ≤ k → k ≤ n-2 →
 pathwidth (@Adj n k) = sourceBound n k
theorem refutes_source_pathwidth_claim : ¬ SourcePathwidthClaim := by
 intro h
 have hh := h 8 4 (by decide) (by decide)
 have hb := johnson_pathwidth_le_40
 rw [hh, source_bound_8_4] at hb
 omega
#print axioms refutes_source_pathwidth_claim
#print axioms decomposition
end JohnsonRefutation
