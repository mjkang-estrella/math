/-
# Bunkbed E7 (r19): direct new-index indicator identities

The two direct new-index membership equivalences for the active branch of the
prefix recurrence `Bun.stf`.  For every `n u j : Nat`, every assignment
`w : Asg n (j+1)` with `u < j+1` and `j+1 < n`, writing

* `p := stf n u j (res n j w)` (the previous level),
* `x := hor (m := j+1) hjn p.1 false w` (horizontal entry into layer 0),
* `y := hor (m := j+1) hjn p.2 true w` (horizontal entry into layer 1),
* `z := w (fresV (n := n) (m := j+1) hjn)` (the vertical bit),

the level-`(j+1)` state of the existing unchanged `Bun.stf` satisfies

* `j+1 ∈ (stf n u (j+1) w).1 ↔ x = true ∨ (z = true ∧ y = true)`,
* `j+1 ∈ (stf n u (j+1) w).2 ↔ y = true ∨ (z = true ∧ x = true)`.

Mechanism: on the active branch the recursion is exactly `stepU`, whose
components are `if (ind x y z).i then insert (j+1) _ else _`; the new index
enters exactly when the corresponding indicator is true (self membership in an
insert; absence from the previous level's component by the paid r9 upper-support
theorem `stf_upper_support`, since every old element is `≤ j`).  The direct
indicator forms are pure Boolean case splits; the coupled `ind_fst`/`ind_snd`
characterizations are not used.  No old-index stability is reproved and no
`Reach` is expanded; below-source, reset and out-of-range branches are not
claimed here.
-/
import BunOldStable
import BunUpperSupport
import BunState

namespace Bun

/-- Direct first-component form of the exact new-index indicator:
`(ind x y z).1 = true ↔ x = true ∨ (z = true ∧ y = true)` — the pure Boolean
core of the direct recurrence, by ordinary kernel cases on the three bits. -/
theorem ind_fst_direct (x y z : Bool) :
    (ind x y z).1 = true ↔ x = true ∨ (z = true ∧ y = true) := by
  cases x <;> cases y <;> cases z <;> simp [ind]

/-- Direct second-component form: `(ind x y z).2 = true ↔ y = true ∨ (z = true ∧ x = true)`. -/
theorem ind_snd_direct (x y z : Bool) :
    (ind x y z).2 = true ↔ y = true ∨ (z = true ∧ x = true) := by
  cases x <;> cases y <;> cases z <;> simp [ind]

/-- The moved index belongs to a one-sided conditional update exactly when the
indicator fires: `m ∈ (if c then insert m T else T) ↔ c = true ∨ m ∈ T`. -/
theorem mem_update_self {m : Nat} {T : Finset Nat} (c : Bool) :
    m ∈ (if c then insert m T else T) ↔ (c = true ∨ m ∈ T) := by
  cases c <;> simp

/-- First component of the pure new-index update: the new index `m` enters
exactly through the first indicator, given it is absent from the carried set. -/
theorem stepU_new_mem_fst (m : Nat) (R S : Finset Nat) (x y z : Bool)
    (hmR : ¬ (m ∈ R)) :
    m ∈ (stepU m R S x y z).1 ↔ x = true ∨ (z = true ∧ y = true) := by
  have h1 : (stepU m R S x y z).1 = if (ind x y z).1 then insert m R else R := rfl
  rw [h1, mem_update_self]
  have hRf : m ∈ R ↔ False := ⟨fun h => absurd h hmR, fun h => False.elim h⟩
  rw [hRf, or_false]
  exact ind_fst_direct x y z

/-- Second component of the pure new-index update: the new index `m` enters
exactly through the second indicator, given it is absent from the carried set. -/
theorem stepU_new_mem_snd (m : Nat) (R S : Finset Nat) (x y z : Bool)
    (hmS : ¬ (m ∈ S)) :
    m ∈ (stepU m R S x y z).2 ↔ y = true ∨ (z = true ∧ x = true) := by
  have h2 : (stepU m R S x y z).2 = if (ind x y z).2 then insert m S else S := rfl
  rw [h2, mem_update_self]
  have hSf : m ∈ S ↔ False := ⟨fun h => absurd h hmS, fun h => False.elim h⟩
  rw [hSf, or_false]
  exact ind_snd_direct x y z

/-- **Direct new-index identity, first component** (the task target): for the
actual active branch `u < j+1 < n` of the prefix recurrence, the new index
`j+1` lies in the first component of `stf n u (j+1) w` exactly when the
horizontal layer-0 entry fires, or the vertical bit fires together with the
horizontal layer-1 entry.  No membership, conclusion-bearing or proxy
assumption beyond `hu` and `hjn`; the absence of `j+1` from the previous level
is derived from the paid upper-support theorem. -/
theorem stf_new_mem_fst_iff (n u j : Nat) (w : Asg n (j+1))
    (hu : u < j + 1) (hjn : j + 1 < n) :
    j + 1 ∈ (stf n u (j+1) w).1 ↔
      hor (m := j+1) hjn (stf n u j (res n j w)).1 false w = true ∨
      (w (fresV (n := n) (m := j+1) hjn) = true ∧
        hor (m := j+1) hjn (stf n u j (res n j w)).2 true w = true) := by
  have hu' : ¬ (j + 1 < u) := by omega
  have heq' : ¬ (j + 1 = u) := by omega
  have hC : stf n u (j+1) w =
      stepU (j+1) (stf n u j (res n j w)).1 (stf n u j (res n j w)).2
        (hor (m := j+1) hjn (stf n u j (res n j w)).1 false w)
        (hor (m := j+1) hjn (stf n u j (res n j w)).2 true w)
        (w (fresV (n := n) (m := j+1) hjn)) := by
    simp only [stf]
    rw [dite_eq_right hu', dite_eq_right heq', dite_eq_left hjn]
  rw [hC]
  have hsupF : ¬ (j + 1 ∈ (stf n u j (res n j w)).1) := by
    intro hmem
    have hle : j + 1 ≤ j := stf_upper_support n u j (j+1) (res n j w) false hmem
    omega
  exact stepU_new_mem_fst (j+1) _ _ _ _ _ hsupF

/-- **Direct new-index identity, second component** (the task target): mirror
of `stf_new_mem_fst_iff` with the two horizontal layers exchanged. -/
theorem stf_new_mem_snd_iff (n u j : Nat) (w : Asg n (j+1))
    (hu : u < j + 1) (hjn : j + 1 < n) :
    j + 1 ∈ (stf n u (j+1) w).2 ↔
      hor (m := j+1) hjn (stf n u j (res n j w)).2 true w = true ∨
      (w (fresV (n := n) (m := j+1) hjn) = true ∧
        hor (m := j+1) hjn (stf n u j (res n j w)).1 false w = true) := by
  have hu' : ¬ (j + 1 < u) := by omega
  have heq' : ¬ (j + 1 = u) := by omega
  have hC : stf n u (j+1) w =
      stepU (j+1) (stf n u j (res n j w)).1 (stf n u j (res n j w)).2
        (hor (m := j+1) hjn (stf n u j (res n j w)).1 false w)
        (hor (m := j+1) hjn (stf n u j (res n j w)).2 true w)
        (w (fresV (n := n) (m := j+1) hjn)) := by
    simp only [stf]
    rw [dite_eq_right hu', dite_eq_right heq', dite_eq_left hjn]
  rw [hC]
  have hsupS : ¬ (j + 1 ∈ (stf n u j (res n j w)).2) := by
    intro hmem
    have hle : j + 1 ≤ j := stf_upper_support n u j (j+1) (res n j w) true hmem
    omega
  exact stepU_new_mem_snd (j+1) _ _ _ _ _ hsupS

end Bun
