/-
# BunFinalWindow — the window factor

For `n`, `j` and any predicate `P` on the `j`-window assignments `Asg n j`, the number
of full outcomes `ω : Out n` whose window restriction `wres n j ω` satisfies `P` equals
`2 ^ c` times the number of window assignments satisfying `P`, where `c` is the number of
tokens outside the window (`tmax t > j`).

Route: `Equiv.piEquivPiSubtypeProd` splits `Out n = Token n → Bool` into the window
function and the off-window function; the fiber over a fixed window assignment has
`2 ^ c` elements.  All decidability is classical.
-/
import BunReachBridge
import BunDomFiber
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace Bun

open Classical

/-- Tokens outside the `j`-window (`tmax t > j`). -/
def outside (n j : Nat) := {t : Token n // ¬ tmax t ≤ j}

noncomputable instance outsideFintype (n j : Nat) : Fintype (outside n j) := by
  unfold outside
  infer_instance

/-- Split an outcome into its window assignment and its off-window assignment. -/
noncomputable def outSplit (n j : Nat) :
    Out n ≃ Asg n j × (outside n j → Bool) :=
  Equiv.piEquivPiSubtypeProd (fun t : Token n => tmax t ≤ j) (fun _ => Bool)

/-- The window component of the split is exactly `wres`. -/
theorem outSplit_fst (n j : Nat) (ω : Out n) :
    (outSplit n j ω).1 = wres n j ω := rfl

/-- **Window factor.**  Counting full outcomes by a window predicate equals
`2 ^ (number of off-window tokens)` times the window-assignment count. -/
theorem window_factor (n j : Nat) (P : Asg n j → Prop) [DecidablePred P] :
    Fintype.card {ω : Out n // P (wres n j ω)} =
      2 ^ Fintype.card (outside n j) * Fintype.card {w : Asg n j // P w} := by
  classical
  have e1 : {ω : Out n // P (wres n j ω)} ≃
      {s : Asg n j × (outside n j → Bool) // P s.1} :=
    Equiv.subtypeEquiv (outSplit n j) (fun ω => by
      show P (wres n j ω) ↔ P ((outSplit n j ω).1)
      rw [outSplit_fst])
  have e2 : {s : Asg n j × (outside n j → Bool) // P s.1} ≃
      {w : Asg n j // P w} × (outside n j → Bool) :=
    Equiv.prodSubtypeFstEquivSubtypeProd
  calc Fintype.card {ω : Out n // P (wres n j ω)}
      = Fintype.card ({w : Asg n j // P w} × (outside n j → Bool)) :=
        Fintype.card_congr (e1.trans e2)
    _ = Fintype.card {w : Asg n j // P w} * Fintype.card (outside n j → Bool) :=
        Fintype.card_prod _ _
    _ = Fintype.card {w : Asg n j // P w} * 2 ^ Fintype.card (outside n j) := by
        rw [Fintype.card_fun, Fintype.card_bool]
    _ = 2 ^ Fintype.card (outside n j) * Fintype.card {w : Asg n j // P w} :=
        Nat.mul_comm _ _

end Bun
