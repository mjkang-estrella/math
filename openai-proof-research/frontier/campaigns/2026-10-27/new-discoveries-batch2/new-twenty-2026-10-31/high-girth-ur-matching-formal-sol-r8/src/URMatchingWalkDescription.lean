module
public import URMatchingWalkLabels
public import URMatchingOrderedCycle
@[expose] public section
namespace URMatching
open scoped Classical
/-- Actual left-started closed simple walks yield occurring coloured descriptions,
including the closing edge. No ordered-cycle premise is supplied. -/
theorem closed_walk_description {N k : ℕ} (σ : PermutationTuples N 100) (u : Fin N)
    (hk : 0 < k) (p : (permutationGraph σ).Walk (.inl u) (.inl u))
    (hlen : p.length = 2*(k+1)) (hn : p.support.tail.Nodup) :
    ∃ w : ValidWitness N k, DescriptionOccurs w.val σ ∧ w.val.1 0 = u := by
  obtain ⟨x,y,hx,hy⟩ := closed_walk_labels σ u p hlen hn
  have ha : ∀ i, (permutationGraph σ).Adj (.inl (x i)) (.inr (y i)) := by
    intro i
    have hi := i.isLt
    have he := p.adj_getVert_succ (i := 2*(k+1)-(2*i.val+1)) (by omega)
    have heq : 2*(k+1)-(2*i.val+1)+1 = 2*(k+1)-2*i.val := by omega
    rw [heq, hx i, hy i] at he
    exact he.symm
  have hb : ∀ i, (permutationGraph σ).Adj (.inl (x (i+1))) (.inr (y i)) := by
    intro i
    have hi := i.isLt
    by_cases hl : i.val+1 < k+1
    · have hv : (i+1).val = i.val+1 := by
        change (i.val + 1 % (k+1)) % (k+1) = i.val+1
        rw [Nat.mod_eq_of_lt (by omega : 1 < k+1), Nat.mod_eq_of_lt hl]
      have he := p.adj_getVert_succ (i := 2*(k+1)-2*(i+1).val) (by omega)
      have heq : 2*(k+1)-2*(i+1).val+1 = 2*(k+1)-(2*i.val+1) := by omega
      rw [heq, hx (i+1), hy i] at he
      exact he
    · have hv : i.val+1 = k+1 := by omega
      have hz : i+1 = 0 := by
        apply Fin.ext
        change (i.val + 1 % (k+1)) % (k+1) = 0
        rw [Nat.mod_eq_of_lt (by omega : 1 < k+1), hv, Nat.mod_self]
      have hzero : x 0 = u := by
        have hh := hx 0
        simp only [Fin.val_zero, Nat.mul_zero, Nat.sub_zero, ← hlen, p.getVert_length,
          Sum.inl.injEq] at hh
        exact hh.symm
      have he := p.adj_getVert_succ (i := 0) (by omega)
      have heq : 2*(k+1)-(2*i.val+1) = 1 := by omega
      have hyi : p.getVert 1 = .inr (y i) := by simpa only [heq] using hy i
      rw [SimpleGraph.Walk.getVert_zero, Nat.zero_add, hyi] at he
      simpa only [hz,hzero] using he
  obtain ⟨w,hwx,_,hw⟩ := ordered_cycle_description σ hk x y ha hb
  refine ⟨w,hw,?_⟩
  rw [hwx]
  have hh := hx 0
  simp only [Fin.val_zero, Nat.mul_zero, Nat.sub_zero, ← hlen, p.getVert_length,
    Sum.inl.injEq] at hh
  exact hh.symm
end URMatching
