/-
# Bunkbed E7 (r18): old-index membership stability of the recursive state

Full old-index stability of the actual recursive `stf` of `BunState`: for all
`n u j k : Nat`, every assignment `w : Asg n (j+1)`, every layer bit `σ` and
every old index `k ≤ j`,

    k ∈ sval σ (stf n u (j+1) w) ↔ k ∈ sval σ (stf n u j (res n j w)),

with no range hypothesis on `n`, `u` or `j`.  Every recursion branch is covered:
the below-source dummies (`j+1 < u`, both sides the dummy pair), the source
reset (`j+1 = u`, where the start-state layers contain at most the new index, so
no old index), the active `stepU` update (`u < j+1 < n`, decided by the paid r17
step lemma `stepU_old_mem_iff`, since `stepU` only ever inserts the new index)
and the out-of-range identity (`u < j+1` with `n ≤ j+1`, where the level equals
the previous one verbatim).  Both layers go through the selector `sval`.
-/
import BunStepOld
import BunState

namespace Bun

/-- Below-source levels are the dummy pair. -/
theorem stf_dummy_of_lt (n u j : Nat) (q : Asg n j) (hju : j < u) :
    stf n u j q = (∅, ∅) := by
  cases j with
  | zero =>
    have hnu : ¬(u = 0) := by omega
    simp only [stf]
    rw [ite_eq_right hnu]
  | succ m =>
    simp only [stf]
    rw [dite_eq_left hju]

/-- The first component of a start state. -/
theorem startST_fst (n j : Nat) (w : Asg n j) :
    (startST n j w).1 = insert j (∅ : Finset Nat) := rfl

/-- The second component of a start state. -/
theorem startST_snd (n j : Nat) (w : Asg n j) :
    (startST n j w).2 =
      if hj : j < n then
        (if w (fresV (n := n) (m := j) hj) then insert j (∅ : Finset Nat) else ∅)
      else ∅ :=
  rfl

/-- The layers of the dummy pair are empty. -/
theorem sval_pair_empty (σ : Bool) : sval σ (∅, ∅) = (∅ : Finset Nat) := by
  cases σ <;> rfl

/-- An index below the start index lies in no layer of the start state. -/
theorem startST_not_mem_old (n j k : Nat) (w : Asg n j) (σ : Bool) (hk : k < j) :
    ¬ (k ∈ sval σ (startST n j w)) := by
  cases σ with
  | false =>
    intro h
    have h' : k ∈ (startST n j w).1 := h
    rw [startST_fst] at h'
    simp only [Finset.mem_insert] at h'
    rcases h' with he | hE
    · omega
    · exact absurd hE (Finset.notMem_empty k)
  | true =>
    intro h
    have h' : k ∈ (startST n j w).2 := h
    rw [startST_snd] at h'
    rcases Nat.lt_or_ge j n with hjn | hnge
    · rw [dite_eq_left hjn] at h'
      by_cases hw : w (fresV (n := n) (m := j) hjn) = true
      · rw [ite_eq_left hw] at h'
        simp only [Finset.mem_insert] at h'
        rcases h' with he | hE
        · omega
        · exact absurd hE (Finset.notMem_empty k)
      · rw [ite_eq_right hw] at h'
        exact absurd h' (Finset.notMem_empty k)
    · have hnge' : ¬(j < n) := by omega
      rw [dite_eq_right hnge'] at h'
      exact absurd h' (Finset.notMem_empty k)

/-- **Old-index membership stability** of the recursive prefix state: for every
window boundary `j`, every layer `σ` and every old index `k ≤ j`, membership in
the level-`(j+1)` state along `w` agrees with membership in the level-`j` state
along the restriction `res n j w`.  No hypothesis on `n`, `u` or `j`. -/
theorem stf_old_mem_iff (n u j k : Nat) (w : Asg n (j+1)) (σ : Bool) (hk : k ≤ j) :
    k ∈ sval σ (stf n u (j+1) w) ↔ k ∈ sval σ (stf n u j (res n j w)) := by
  rcases Nat.lt_or_ge (j+1) u with hlt | hge
  · -- below the source: both levels are dummy pairs
    have hju : j < u := by omega
    rw [stf_dummy_of_lt n u (j+1) w hlt, stf_dummy_of_lt n u j (res n j w) hju]
  · by_cases heq : j+1 = u
    · -- source reset: start state against the dummy pair
      have hu : ¬(j+1 < u) := by omega
      have hju : j < u := by omega
      have hL : stf n u (j+1) w = startST n (j+1) w := by
        simp only [stf]
        rw [dite_eq_right hu, dite_eq_left heq]
      rw [hL, stf_dummy_of_lt n u j (res n j w) hju]
      have hLnot := startST_not_mem_old n (j+1) k w σ (by omega)
      have hRnot : ¬(k ∈ sval σ (∅, ∅)) := by
        rw [sval_pair_empty]
        intro hh
        exact absurd hh (Finset.notMem_empty k)
      exact ⟨fun h => absurd h hLnot, fun h => absurd h hRnot⟩
    · -- past the source: active update or verbatim carry
      have hu' : ¬(j+1 < u) := by omega
      have heq' : ¬(j+1 = u) := by omega
      rcases Nat.lt_or_ge (j+1) n with hjn | hge'n
      · -- active update at the new index `j+1`
        have hC : stf n u (j+1) w =
            stepU (j+1) (stf n u j (res n j w)).1 (stf n u j (res n j w)).2
              (hor (m := j+1) hjn (stf n u j (res n j w)).1 false w)
              (hor (m := j+1) hjn (stf n u j (res n j w)).2 true w)
              (w (fresV (n := n) (m := j+1) hjn)) := by
          simp only [stf]
          rw [dite_eq_right hu', dite_eq_right heq', dite_eq_left hjn]
        rw [hC]
        exact stepU_old_mem_iff (j+1) k _ _ _ _ _ _ (by omega)
      · -- out of range: the level equals the previous one verbatim
        have hnle : ¬(j+1 < n) := by omega
        have hC : stf n u (j+1) w = stf n u j (res n j w) := by
          simp only [stf]
          rw [dite_eq_right hu', dite_eq_right heq', dite_eq_right hnle]
        rw [hC]

end Bun
