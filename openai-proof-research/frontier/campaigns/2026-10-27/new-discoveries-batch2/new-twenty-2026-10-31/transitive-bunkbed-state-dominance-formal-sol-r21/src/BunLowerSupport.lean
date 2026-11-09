/-
# Bunkbed E7 (r15): lower support of the prefix state

Theorem `stf_lower_support` (the single target of this task): for the existing,
unchanged `Bun.stf` and `Bun.sval`, arbitrary `n u j k : Nat`, `w : Asg n j` and
`sigma : Bool`, `k ∈ sval sigma (stf n u j w)` implies `u ≤ k`.

Mechanism: componentwise induction on `j` along the exact recursion, no
enumeration.  The start state contributes only the index `j` itself, via the
r14 fact `startST_support`; the update `stepU` either keeps a component or
inserts `j+1`, via the r12 fact `stepU_lower_closed`; below-source and dummy
states are empty, so those branches are vacuous.
-/
import BunState
import BunStartSupport
import BunStepLower

namespace Bun

/-- Both components of the prefix state `stf n u j w` only contain indices `≥ u`. -/
theorem stf_lower_parts (n u : Nat) : ∀ (j : Nat) (w : Asg n j),
    (∀ k : Nat, k ∈ (stf n u j w).1 → u ≤ k) ∧
    (∀ k : Nat, k ∈ (stf n u j w).2 → u ≤ k) := by
  intro j
  induction j with
  | zero =>
    intro w
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [stf] at hk
      split at hk
      · rename_i hu
        have hk0 : k = 0 := startST_support n 0 k w false hk
        omega
      · simp at hk
    · intro k hk
      simp only [stf] at hk
      split at hk
      · rename_i hu
        have hk0 : k = 0 := startST_support n 0 k w true hk
        omega
      · simp at hk
  | succ j ih =>
    intro w
    have hP := ih (res n j w)
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [stf] at hk
      split at hk
      · simp at hk
      · rename_i h1
        split at hk
        · rename_i h2
          have hk1 : k = j + 1 := startST_support n (j + 1) k w false hk
          omega
        · have hu1 : u ≤ j + 1 := by omega
          have hR : ∀ a : Nat, a ∈ (stf n u j (res n j w)).1 → u ≤ a := fun a ha => hP.1 a ha
          have hS : ∀ a : Nat, a ∈ (stf n u j (res n j w)).2 → u ≤ a := fun a ha => hP.2 a ha
          split at hk
          · rename_i hjn
            exact stepU_lower_closed (j + 1) u k (stf n u j (res n j w)).1
              (stf n u j (res n j w)).2
              (hor (m := j + 1) hjn (stf n u j (res n j w)).1 false w)
              (hor (m := j + 1) hjn (stf n u j (res n j w)).2 true w)
              (w (fresV (n := n) (m := j + 1) hjn)) false hR hS hu1 hk
          · exact hP.1 k hk
    · intro k hk
      simp only [stf] at hk
      split at hk
      · simp at hk
      · rename_i h1
        split at hk
        · rename_i h2
          have hk1 : k = j + 1 := startST_support n (j + 1) k w true hk
          omega
        · have hu1 : u ≤ j + 1 := by omega
          have hR : ∀ a : Nat, a ∈ (stf n u j (res n j w)).1 → u ≤ a := fun a ha => hP.1 a ha
          have hS : ∀ a : Nat, a ∈ (stf n u j (res n j w)).2 → u ≤ a := fun a ha => hP.2 a ha
          split at hk
          · rename_i hjn
            exact stepU_lower_closed (j + 1) u k (stf n u j (res n j w)).1
              (stf n u j (res n j w)).2
              (hor (m := j + 1) hjn (stf n u j (res n j w)).1 false w)
              (hor (m := j + 1) hjn (stf n u j (res n j w)).2 true w)
              (w (fresV (n := n) (m := j + 1) hjn)) true hR hS hu1 hk
          · exact hP.2 k hk

/-- **Lower support** (the task target): membership in the selected component of
the prefix state is bounded below by the source index. -/
theorem stf_lower_support (n u j k : Nat) (w : Asg n j) (sigma : Bool)
    (hk : k ∈ sval sigma (stf n u j w)) : u ≤ k := by
  have hparts := stf_lower_parts n u j w
  cases sigma with
  | false => exact hparts.1 k hk
  | true => exact hparts.2 k hk

end Bun
