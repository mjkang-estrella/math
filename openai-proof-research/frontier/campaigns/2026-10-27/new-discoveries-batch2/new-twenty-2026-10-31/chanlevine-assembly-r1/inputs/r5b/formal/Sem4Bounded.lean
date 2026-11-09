import SemFinal2
open scoped BigOperators
namespace ChanLevine.Sem4
variable {n : ℕ} [NeZero n]

/-- A terminal execution under arbitrary per-vertex firing quotas. -/
def QuotaTerminal (c : SignedConfig n) (quota : ZMod n → ℕ)
    (w : List (ZMod n)) (d : SignedConfig n) : Prop :=
  LegalWord c w d ∧ (∀ v, w.count v ≤ quota v) ∧
    ∀ v, w.count v < quota v → d.x v ≤ 0

/-- Finite quotas always admit a maximal legal execution. No cycle test is used. -/
theorem quota_terminal_exists (c : SignedConfig n) (quota : ZMod n → ℕ) :
    ∃ w d, QuotaTerminal c quota w d := by
  classical
  generalize he : ∑ v, quota v = fuel
  induction fuel using Nat.strong_induction_on generalizing c quota with
  | h fuel ih =>
    by_cases hs : ∃ a, 0 < quota a ∧ 0 < c.x a
    · obtain ⟨a, hq, ha⟩ := hs
      let q' := Function.update quota a (quota a - 1)
      have hsum : (∑ v, q' v) < fuel := by
        have hpoint : ∀ v, q' v + (if v = a then 1 else 0) = quota v := by
          intro v
          by_cases hv : v = a
          · subst v; simp [q']; omega
          · simp [q', hv]
        have htotal := congrArg (fun f : ZMod n → ℕ => ∑ v, f v) (funext hpoint)
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true] at htotal
        omega
      obtain ⟨w, d, hl, hb, ht⟩ := ih _ hsum (fire c a) q' rfl
      refine ⟨a :: w, d, .cons a ha hl, ?_, ?_⟩
      · intro v
        have hv := hb v
        by_cases heq : a = v
        · subst v; simp [q'] at hv
          simp only [List.count_cons_self]; omega
        · simpa [List.count_cons_of_ne heq, q', Ne.symm heq] using hv
      · intro v hv
        apply ht v
        by_cases heq : a = v
        · subst v
          simp only [List.count_cons_self] at hv
          simp [q']; omega
        · simpa [List.count_cons_of_ne heq, q', Ne.symm heq] using hv
    · refine ⟨[], c, .nil _, by simp, ?_⟩
      intro v hv
      have hnv : ¬ (0 < quota v ∧ 0 < c.x v) := fun h => hs ⟨v, h⟩
      simp only [List.count_nil] at hv
      omega

/-- The bounded search proposed in the brief exists for every starting state. -/
theorem capped_terminal_exists (c : SignedConfig n) :
    ∃ w d, LegalWord c w d ∧ (∀ v, w.count v ≤ 2) ∧
      ∀ v, w.count v < 2 → d.x v ≤ 0 :=
  quota_terminal_exists c (fun _ => 2)

omit [NeZero n] in
/-- For a natural starting state every uncapped vertex is empty at termination. -/
theorem capped_terminal_empty {c : Config n} {d : SignedConfig n}
    {w : List (ZMod n)} (h : QuotaTerminal c.lift (fun _ => 2) w d)
    {v : ZMod n} (hv : w.count v < 2) : d.x v = 0 := by
  have hn := h.1.nonnegative (k := v) (by simp [Config.lift])
  have ht := h.2.2 v hv
  omega
end ChanLevine.Sem4
