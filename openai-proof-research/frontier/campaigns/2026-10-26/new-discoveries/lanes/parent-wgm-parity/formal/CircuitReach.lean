import FlowParity

open scoped BigOperators

namespace WGMParity

def CircuitFeasible {L I : Type*} (child : I × Bool → L ⊕ I)
    (x : L ⊕ I → ℝ) : Prop :=
  ∀ i, x (Sum.inr i) ^ 2 ≤ x (child (i, false)) * x (child (i, true))

def CircuitSound {L I : Type*} [Fintype L] (s : L → ℕ) (root : I)
    (child : I × Bool → L ⊕ I) : Prop :=
  ∀ x : L ⊕ I → ℝ, (∀ v, 0 ≤ x v) → CircuitFeasible child x →
    x (Sum.inr root) ^ (∑ j, s j) ≤ ∏ j, x (Sum.inl j) ^ s j

def CircuitEdge {L I : Type*} (child : I × Bool → L ⊕ I)
    (u v : L ⊕ I) : Prop := ∃ i b, u = Sum.inr i ∧ child (i, b) = v

def CircuitReach {L I : Type*} (root : I) (child : I × Bool → L ⊕ I)
    (v : L ⊕ I) : Prop := Relation.ReflTransGen (CircuitEdge child) (Sum.inr root) v

theorem circuitReach_root {L I : Type*} (root : I) (child : I × Bool → L ⊕ I) :
    CircuitReach root child (Sum.inr root) := .refl

theorem circuitReach_child {L I : Type*} (root : I) (child : I × Bool → L ⊕ I)
    {i : I} (hi : CircuitReach root child (Sum.inr i)) (b : Bool) :
    CircuitReach root child (child (i, b)) := hi.tail ⟨i, b, rfl, rfl⟩

theorem circuitSound_reaches_leaf {L I : Type*} [Fintype L]
    (s : L → ℕ) (hs : ∀ j, 0 < s j) (root : I)
    (child : I × Bool → L ⊕ I) (h : CircuitSound s root child) (j : L) :
    CircuitReach root child (Sum.inl j) := by
  classical
  by_contra hj
  let x : L ⊕ I → ℝ := fun v => if CircuitReach root child v then 1 else 0
  have hx : ∀ v, 0 ≤ x v := by intro v; dsimp [x]; split_ifs <;> norm_num
  have hf : CircuitFeasible child x := by
    intro i
    by_cases hi : CircuitReach root child (Sum.inr i)
    · have h0 := circuitReach_child root child hi false
      have h1 := circuitReach_child root child hi true
      simp [x, hi, h0, h1]
    · have := mul_nonneg (hx (child (i, false))) (hx (child (i, true)))
      simpa [x, hi] using this
  have hp : (∏ k, x (Sum.inl k) ^ s k) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [x, hj, Nat.ne_of_gt (hs j)]
  have hh := h x hx hf
  rw [hp] at hh
  have hr := circuitReach_root root child
  norm_num [x, hr] at hh

theorem circuitReach_last {L I : Type*} (root : I) (child : I × Bool → L ⊕ I)
    {v : L ⊕ I} (hv : CircuitReach root child v) :
    v = Sum.inr root ∨ ∃ i b, CircuitReach root child (Sum.inr i) ∧ child (i, b) = v := by
  rcases hv.cases_tail with h | ⟨u, hu, i, b, rfl, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, b, hu, hc⟩

end WGMParity
