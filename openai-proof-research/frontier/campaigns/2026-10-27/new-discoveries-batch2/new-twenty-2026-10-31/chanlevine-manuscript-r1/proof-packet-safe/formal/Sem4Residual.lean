import Sem4Balance
namespace ChanLevine.Sem4

/-- REMAINING, not asserted: an incomplete capped execution traps a nonempty
chip-free set under the *initial* rotors. The missing proof is a residual-flux
balance argument, independent of the cycle test. -/
def CappedDeficitTrap : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (c : Config n)
    (w : List (ZMod n)) (d : SignedConfig n),
    QuotaTerminal c.lift (fun _ => 2) w d →
    (∃ v, w.count v < 2) →
    ∃ S : Set (ZMod n), S.Nonempty ∧ (∀ v ∈ S, c.x v = 0) ∧
      ∀ v ∈ S, rotorNext c v ∈ S

/-- CONDITIONAL: the precise remaining deficit-trap lemma completes the capped search. -/
theorem capped_completion (htrap : CappedDeficitTrap)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) {c : Config n} (hc : CycleTest c)
    {w : List (ZMod n)} {d : SignedConfig n}
    (h : QuotaTerminal c.lift (fun _ => 2) w d) : ∀ v, w.count v = 2 := by
  intro v
  have hb := h.2.1 v
  change w.count v ≤ 2 at hb
  by_contra he
  have hv : w.count v < 2 := by omega
  obtain ⟨S, hs, hx, hq⟩ := htrap n hn c w d h ⟨v, hv⟩
  exact no_empty_rotor_closed_set hc hs hx hq

/-- CONDITIONAL on one explicit local residual-flux obligation. -/
theorem cycleTestWord (htrap : CappedDeficitTrap) : CycleTestWord := by
  intro n inst hn c hc
  obtain ⟨w, d, ht⟩ := quota_terminal_exists c.lift (fun _ => 2)
  have hb := capped_completion htrap hn hc ht
  have hne : w ≠ [] := by
    intro he
    have h := hb 0
    simp [he] at h
  exact ⟨w, hne, (balanced_return ht.1 hb) ▸ ht.1⟩
end ChanLevine.Sem4
