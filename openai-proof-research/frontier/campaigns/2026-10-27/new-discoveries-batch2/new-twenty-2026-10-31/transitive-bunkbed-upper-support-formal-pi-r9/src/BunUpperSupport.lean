/-
# Bunkbed E7 (r9): upper support of the prefix state

Theorem `stf_upper_support` (the single target of this task): for the existing,
unchanged `Bun.stf` and `Bun.sval`, arbitrary `n u j k : Nat`, `w : Asg n j` and
`sigma : Bool`, `k ∈ sval sigma (stf n u j w)` implies `k ≤ j`.

Mechanism: both components of `stf n u j w` are subsets of `Finset.range (j+1)`
(induction on `j`; `startST` contributes only the index `j` itself, `stepU`
either keeps a component or inserts `j+1`), and `sval` only selects one of the
two components.
-/
import BunState

namespace Bun

/-- Both components of `startST n j w` are contained in `Finset.range (j+1)`. -/
theorem startST_parts_range (n j : Nat) (w : Asg n j) :
    (startST n j w).1 ⊆ Finset.range (j + 1) ∧ (startST n j w).2 ⊆ Finset.range (j + 1) := by
  have h1 : (startST n j w).1 = insert j ∅ := rfl
  have h2 : (startST n j w).2 =
      if hj : j < n then (if w (fresV (n := n) (m := j) hj) then insert j ∅ else ∅) else ∅ := rfl
  rw [h1, h2]
  constructor
  · intro k hk
    rcases Finset.mem_insert.1 hk with h | h
    · exact Finset.mem_range.2 (by omega)
    · simp at h
      exact False.elim h
  · intro k hk
    split at hk
    · split at hk
      · rcases Finset.mem_insert.1 hk with h | h
        · exact Finset.mem_range.2 (by omega)
        · simp at h
          exact False.elim h
    · simp at hk
      exact False.elim hk

/-- Both components of the prefix state `stf n u j w` are contained in
`Finset.range (j+1)`, i.e. every index occurring in them is `≤ j`. -/
theorem stf_parts_range (n u : Nat) : ∀ (j : Nat) (w : Asg n j),
    (stf n u j w).1 ⊆ Finset.range (j + 1) ∧ (stf n u j w).2 ⊆ Finset.range (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro w
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [stf] at hk
      split at hk
      · exact (startST_parts_range n 0 w).1 hk
      · simp at hk
        exact False.elim hk
    · intro k hk
      simp only [stf] at hk
      split at hk
      · exact (startST_parts_range n 0 w).2 hk
      · simp at hk
        exact False.elim hk
  | succ j ih =>
    intro w
    have hP := ih (res n j w)
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [stf] at hk
      split at hk
      · simp at hk
        exact False.elim hk
      · rename_i h1
        split at hk
        · exact (startST_parts_range n (j + 1) w).1 hk
        · rename_i h2
          have hule : u ≤ j := by omega
          split at hk
          · simp only [stepU] at hk
            split at hk
            · rcases Finset.mem_insert.1 hk with h | h
              · exact Finset.mem_range.2 (by omega)
              · have hlt := Finset.mem_range.1 (hP.1 h)
                exact Finset.mem_range.2 (by omega)
            · have hlt := Finset.mem_range.1 (hP.1 hk)
              exact Finset.mem_range.2 (by omega)
          · have hlt := Finset.mem_range.1 (hP.1 hk)
            exact Finset.mem_range.2 (by omega)
    · intro k hk
      simp only [stf] at hk
      split at hk
      · simp at hk
        exact False.elim hk
      · rename_i h1
        split at hk
        · exact (startST_parts_range n (j + 1) w).2 hk
        · rename_i h2
          have hule : u ≤ j := by omega
          split at hk
          · simp only [stepU] at hk
            split at hk
            · rcases Finset.mem_insert.1 hk with h | h
              · exact Finset.mem_range.2 (by omega)
              · have hlt := Finset.mem_range.1 (hP.2 h)
                exact Finset.mem_range.2 (by omega)
            · have hlt := Finset.mem_range.1 (hP.2 hk)
              exact Finset.mem_range.2 (by omega)
          · have hlt := Finset.mem_range.1 (hP.2 hk)
            exact Finset.mem_range.2 (by omega)

/-- **Upper support** (the task target): membership in the selected component of
the prefix state is bounded by the window index. -/
theorem stf_upper_support (n u j k : Nat) (w : Asg n j) (sigma : Bool)
    (hk : k ∈ sval sigma (stf n u j w)) : k ≤ j := by
  cases sigma
  · simp only [sval] at hk
    have h := Finset.mem_range.1 ((stf_parts_range n u j w).1 hk)
    omega
  · simp only [sval] at hk
    have h := Finset.mem_range.1 ((stf_parts_range n u j w).2 hk)
    omega

end Bun
