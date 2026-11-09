/-
# Bunkbed E7 (r2): bridge, part 1 — the window assignment of an outcome.

`wres n j ω` is the window-`j` assignment obtained by reading `ω` on the
window tokens; `wres_apply` is its defining equation.  The remaining bridge
(RT-derivation induction, level bounds, count kernel, endpoint) is specified
in CHECKPOINT.md.
-/
import BunkbedBase
import BunState
import BunReach

namespace Bun

/-- The window-`j` assignment induced by the outcome. -/
def wres (n j : Nat) (ω : Out n) : Asg n j := fun t => ω t.1

theorem wres_apply {n j : Nat} (ω : Out n) (t : Win n j) : wres n j ω t = ω t.1 := rfl

/-- The window assignment restricts: `wres n j ω = res n j (wres n (j+1) ω)`. -/
theorem wres_res {n j : Nat} (ω : Out n) :
    wres n j ω = res n j (wres n (j+1) ω) := by
  unfold wres res
  funext t
  rfl

/-- Window agreement from outcome agreement on `tmax ≤ j`. -/
theorem wres_agree {n j : Nat} {ω ω' : Out n}
    (hag : ∀ t : Token n, tmax t ≤ j → ω t = ω' t) : wres n j ω = wres n j ω' := by
  unfold wres
  funext t
  exact hag _ t.2

end Bun
