/-
# BunFinalEndpoint — the literal bunkbed inequality for transitive tournaments (E7)

`Bun.bunkbed_E7_transitive`: for every `n` and every pair of indices `u v : Fin n`, the
number of outcomes in which `(v, true)` is reachable from `(u, false)` is at most the
number in which `(v, false)` is.

Proof.  If `v < u`, index monotonicity of `Reach` empties both events.  Otherwise
`u ≤ v`, and `stf_reach_endpoint` identifies each event with membership of `v` in the
corresponding component of the prefix state at window `v`.  The window factor
(`Bun.window_factor`, module `BunFinalWindow`) rewrites both counts as
`2 ^ (off-window tokens)` times the corresponding window-assignment counts, and
`Bun.state_endpoint` (module `BunDomFinal`) supplies the window-level inequality.
-/
import BunFinalWindow
import BunDomFinal
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic

namespace Bun

open Classical

open Classical in
/-- **The bunkbed conjecture in the E7 model for transitive tournaments.** -/
theorem bunkbed_E7_transitive (n : Nat) (u v : Fin n) :
    Fintype.card {ω : Out n // Reach n ω (u, false) (v, true)} ≤
    Fintype.card {ω : Out n // Reach n ω (u, false) (v, false)} := by
  classical
  by_cases hlt : (v : Nat) < (u : Nat)
  · have h1 : Fintype.card {ω : Out n // Reach n ω (u, false) (v, true)} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun x => reach_of_lt n x.1 u v true hlt x.2⟩
    have h2 : Fintype.card {ω : Out n // Reach n ω (u, false) (v, false)} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun x => reach_of_lt n x.1 u v false hlt x.2⟩
    rw [h1, h2]
  · have huv : (u : Nat) ≤ (v : Nat) := Nat.le_of_not_lt hlt
    have hv : (v : Nat) < n := v.isLt
    have e1 : {ω : Out n // Reach n ω (u, false) (v, true)} ≃
        {ω : Out n // (v : Nat) ∈ sval true
          (stf n (u : Nat) (v : Nat) (wres n (v : Nat) ω))} :=
      Equiv.subtypeEquivRight (fun ω => (stf_reach_endpoint n u v true ω).symm)
    have e2 : {ω : Out n // Reach n ω (u, false) (v, false)} ≃
        {ω : Out n // (v : Nat) ∈ sval false
          (stf n (u : Nat) (v : Nat) (wres n (v : Nat) ω))} :=
      Equiv.subtypeEquivRight (fun ω => (stf_reach_endpoint n u v false ω).symm)
    have h1 : Fintype.card {ω : Out n // Reach n ω (u, false) (v, true)} =
        2 ^ Fintype.card (outside n (v : Nat)) *
          Fintype.card {w : Asg n (v : Nat) //
            (v : Nat) ∈ sval true (stf n (u : Nat) (v : Nat) w)} :=
      (Fintype.card_congr e1).trans
        (window_factor n (v : Nat)
          (fun w => (v : Nat) ∈ sval true (stf n (u : Nat) (v : Nat) w)))
    have h2 : Fintype.card {ω : Out n // Reach n ω (u, false) (v, false)} =
        2 ^ Fintype.card (outside n (v : Nat)) *
          Fintype.card {w : Asg n (v : Nat) //
            (v : Nat) ∈ sval false (stf n (u : Nat) (v : Nat) w)} :=
      (Fintype.card_congr e2).trans
        (window_factor n (v : Nat)
          (fun w => (v : Nat) ∈ sval false (stf n (u : Nat) (v : Nat) w)))
    have hs := state_endpoint n (u : Nat) (v : Nat) huv hv
    calc Fintype.card {ω : Out n // Reach n ω (u, false) (v, true)}
        = 2 ^ Fintype.card (outside n (v : Nat)) *
            Fintype.card {w : Asg n (v : Nat) //
              (v : Nat) ∈ sval true (stf n (u : Nat) (v : Nat) w)} := h1
      _ ≤ 2 ^ Fintype.card (outside n (v : Nat)) *
            Fintype.card {w : Asg n (v : Nat) //
              (v : Nat) ∈ sval false (stf n (u : Nat) (v : Nat) w)} :=
          Nat.mul_le_mul_left (2 ^ Fintype.card (outside n (v : Nat))) hs
      _ = Fintype.card {ω : Out n // Reach n ω (u, false) (v, false)} := h2.symm

end Bun
