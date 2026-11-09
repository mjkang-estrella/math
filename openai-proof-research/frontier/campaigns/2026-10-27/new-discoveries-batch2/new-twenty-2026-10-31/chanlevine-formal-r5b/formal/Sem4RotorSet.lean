import Sem4Bounded
namespace ChanLevine.Sem4
variable {n : ℕ} [NeZero n]

/-- The edge of the initial rotor, before advancing it. -/
def rotorNext (c : Config n) (v : ZMod n) : ZMod n :=
  if c.q v then v + 1 else v - 1

/-- A cycle-test state has no nonempty, chip-free set closed under its rotors.
This is proved directly on the cycle, without the general network cycle test. -/
theorem no_empty_rotor_closed_set {c : Config n} (hc : CycleTest c)
    {S : Set (ZMod n)} (hne : S.Nonempty)
    (hempty : ∀ v ∈ S, c.x v = 0)
    (hclosed : ∀ v ∈ S, rotorNext c v ∈ S) : False := by
  obtain ⟨a, ha⟩ := hne
  cases hqa : c.q a with
  | true =>
    have hs : ∀ v ∈ S, c.q v = true → (v+1 ∈ S ∧ c.q (v+1) = true) := by
      intro v hv hq
      have hn : v+1 ∈ S := by simpa [rotorNext, hq] using hclosed v hv
      refine ⟨hn, ?_⟩
      cases he : c.q (v+1) with
      | true => rfl
      | false =>
        obtain h | h := hc.1 v hq he
        · exact False.elim (h (hempty v hv))
        · exact False.elim (h (hempty (v+1) hn))
    have hall : ∀ t : ℕ, a + (t : ZMod n) ∈ S ∧ c.q (a + (t : ZMod n)) = true := by
      intro t
      induction t with
      | zero => simpa using And.intro ha hqa
      | succ t ih => simpa [Nat.cast_add, add_assoc] using hs _ ih.1 ih.2
    have hglobal : ∀ v, v ∈ S ∧ c.q v = true := by
      intro v
      simpa using hall (v-a).val
    obtain ⟨v, hv⟩ := hc.2.1 (fun v => (hglobal v).2)
    exact hv (hempty v (hglobal v).1)
  | false =>
    have hs : ∀ v ∈ S, c.q v = false → (v-1 ∈ S ∧ c.q (v-1) = false) := by
      intro v hv hq
      have hn : v-1 ∈ S := by simpa [rotorNext, hq] using hclosed v hv
      refine ⟨hn, ?_⟩
      cases he : c.q (v-1) with
      | false => rfl
      | true =>
        have heq : v-1+1 = v := by ring
        have hpair := hc.1 (v-1) he (by simpa [heq] using hq)
        rcases hpair with h | h
        · exact False.elim (h (hempty (v-1) hn))
        · exact False.elim (h (by simpa [heq] using hempty v hv))
    have hall : ∀ t : ℕ, a - (t : ZMod n) ∈ S ∧ c.q (a - (t : ZMod n)) = false := by
      intro t
      induction t with
      | zero => simpa using And.intro ha hqa
      | succ t ih => simpa [Nat.cast_add, sub_add_eq_sub_sub] using hs _ ih.1 ih.2
    have hglobal : ∀ v, v ∈ S ∧ c.q v = false := by
      intro v
      have heq : a - (a-v) = v := by ring
      simpa [heq] using hall (a-v).val
    obtain ⟨v, hv⟩ := hc.2.2 (fun v => (hglobal v).2)
    exact hv (hempty v (hglobal v).1)
end ChanLevine.Sem4
