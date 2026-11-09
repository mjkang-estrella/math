/-
# Bunkbed E7 (r2): prefix state dynamics

Window `Win n j` = tokens with `tmax t ≤ j`; `Asg n j` = Boolean assignments to that
window.  For a source index `u`, `stf n u j w` is the pair of sets of indices `≤ j`
whose layer-0 / layer-1 copies are reachable from `(u,false)` using only the prefix `w`;
it is defined by the exact new-index closure.  The new indicator pair is
`(if z then x||y else x, if z then x||y else y)` with `x,y` the horizontal-entry
disjunctions and `z` the new vertical bit.

Bridge (later lemmas): for any two full outcomes agreeing on the window `j`, literal
`Reach` from `(u,false)` to any index-`≤ j` vertex agrees, and `Reach` into `(j,σ)`
holds iff `j` lies in the corresponding state set.  No counting here.
-/
import BunkbedCount
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Card

namespace Bun

/-- Tokens of `tmax ≤ j`. -/
def Win (n j : Nat) := {t : Token n // tmax t ≤ j}

/-- Assignments to the `j`-window. -/
def Asg (n j : Nat) := Win n j → Bool

/-- Restrict a `(j+1)`-prefix to the `j`-window. -/
def res (n j : Nat) (w : Asg n (j+1)) : Asg n j :=
  fun t => w ⟨t.1, Nat.le_trans t.2 (Nat.le_succ j)⟩

/-- Horizontal fresh token `(i,m,l)` seen as a window-`m` element (`m < n`, `i < m`). -/
def fresH {n m : Nat} (hm : m < n) (i : Nat) (hic : i < m) (l : Bool) : Win n m :=
  ⟨htok (⟨i, by omega⟩ : Fin n) (⟨m, hm⟩ : Fin n) hic l, by simp [htok, tmax]⟩

/-- Vertical fresh token of index `m` seen as a window-`m` element (`m < n`). -/
def fresV {n m : Nat} (hm : m < n) : Win n m :=
  ⟨Sum.inr (⟨m, hm⟩ : Fin n), by simp [tmax]⟩

/-- Horizontal-entry disjunction into layer `l` at new index `m`, from reachable set `R`. -/
def hor {n m : Nat} (hm : m < n) (R : Finset Nat) (l : Bool) (w : Asg n m) : Bool :=
  decide (((Finset.range m).attach.filter
    fun t : {x // x ∈ Finset.range m} =>
      decide (t.1 ∈ R) && w (fresH hm t.1 (Finset.mem_range.mp t.2) l)).Nonempty)

/-- The exact new-index indicator pair, closed form. -/
def ind (x y z : Bool) : Bool × Bool :=
  (if z then x || y else x, if z then x || y else y)

/-- Pure new-index set update. -/
def stepU (m : Nat) (R S : Finset Nat) (x y z : Bool) : Finset Nat × Finset Nat :=
  let a := (ind x y z).1
  let b := (ind x y z).2
  ((if a then insert m R else R), (if b then insert m S else S))

/-- The start state at index `j` (used at `j = u`): the layer-0 copy is reachable by
reflexivity; the layer-1 copy exactly through the vertical bit. -/
def startST (n j : Nat) (w : Asg n j) : Finset Nat × Finset Nat :=
  (insert j ∅,
    if hj : j < n then (if w (fresV (n := n) (m := j) hj) then insert j ∅ else ∅) else ∅)

/-- Prefix state: sets of indices `≤ j` whose layer-0/1 copies are reachable from
`(u,false)` within the prefix `w`.  Off the strip `u ≤ · ≤ v < n` values are dummies. -/
def stf (n u : Nat) : (j : Nat) → Asg n j → Finset Nat × Finset Nat
  | 0, w => if u = 0 then startST n 0 w else (∅, ∅)
  | j+1, w =>
      if _h1 : j + 1 < u then (∅, ∅)
      else if _h2 : j + 1 = u then startST n (j+1) w
      else
        let p := stf n u j (res n j w)
        if hjn : j + 1 < n then
          stepU (j+1) p.1 p.2
            (hor (m := j+1) hjn p.1 false w)
            (hor (m := j+1) hjn p.2 true w)
            (w (fresV (n := n) (m := j+1) hjn))
        else p

/-- Selector of the layer-`σ` component. -/
def sval (σ : Bool) (p : Finset Nat × Finset Nat) : Finset Nat :=
  if σ then p.2 else p.1

end Bun
