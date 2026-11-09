import Sem3Coverage
namespace ChanLevine.Sem3
variable {n : ℕ}

def EmptyPair (c : SignedConfig n) (k : ZMod n) : Prop :=
  c.x k = 0 ∧ c.x (k+1) = 0 ∧ c.q k = true ∧ c.q (k+1) = false

theorem emptyPair_back {c : SignedConfig n} {k a : ZMod n}
    (hneq : k+1 ≠ k) (hc : ∀ j, 0 ≤ c.x j) (ha : 0 < c.x a)
    (he : EmptyPair (fire c a) k) : a ≠ k ∧ a ≠ k+1 ∧ EmptyPair c k := by
  obtain ⟨hx, hy, hq, hr⟩ := he
  have hak : a ≠ k := by
    intro heq; subst a
    have hq' : c.q k = false := by simpa [fire] using hq
    have htar : target c k = k+1 := by simp [target, hq']
    have hh := hc (k+1)
    simp [fire, hneq, htar] at hy
    omega
  have hal : a ≠ k+1 := by
    intro heq; subst a
    have hq' : c.q (k+1) = true := by simpa [fire] using hr
    have htar : target c (k+1) = k := by simp [target, hq']
    have hh := hc k
    simp [fire, Ne.symm hneq, htar] at hx
    omega
  refine ⟨hak, hal, ?_, ?_, ?_, ?_⟩
  · have hh := hc k
    simp only [fire, Ne.symm hak, ite_false, sub_zero] at hx
    split_ifs at hx <;> omega
  · have hh := hc (k+1)
    simp only [fire, Ne.symm hal, ite_false, sub_zero] at hy
    split_ifs at hy <;> omega
  · simpa [fire, Ne.symm hak] using hq
  · simpa [fire, Ne.symm hal] using hr

theorem emptyPair_word {c d : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w d) (k : ZMod n) (hneq : k+1 ≠ k)
    (hc : ∀ j, 0 ≤ c.x j) (he : EmptyPair d k) : EmptyPair c k ∧ k ∉ w := by
  induction h with
  | nil => exact ⟨he, by simp⟩
  | @cons c d w a ha hw ih =>
    have hnn : ∀ j, 0 ≤ (fire c a).x j := fun j => nonnegative_fire_at ha (hc j)
    obtain ⟨hp, hn⟩ := ih hnn he
    obtain ⟨hak, _, hb⟩ := emptyPair_back hneq hc ha hp
    exact ⟨hb, by simpa [Ne.symm hak] using hn⟩

theorem closedWordCycleTest : ClosedWordCycleTest := by
  intro n inst hn c w hw h
  have hone : (1 : ZMod n) ≠ 0 := by
    intro hh
    have hh' := congrArg ZMod.val hh
    rw [ZMod.val_one'' (by omega)] at hh'
    simp at hh'
  have hnn : ∀ j, 0 ≤ c.lift.x j := fun j => Int.natCast_nonneg (c.x j)
  have hex : ∃ k, c.x k ≠ 0 := by
    cases h with
    | nil => exact False.elim (hw rfl)
    | cons a ha _ => exact ⟨a, by change 0 < (c.x a : ℤ) at ha; omega⟩
  refine ⟨?_, fun _ => hex, fun _ => hex⟩
  intro k hk hl
  by_contra hb
  have hx : c.x k = 0 ∧ c.x (k+1) = 0 := by tauto
  have hneq : k+1 ≠ k := by intro he; apply hone; exact add_left_cancel (he.trans (add_zero k).symm)
  have hp : EmptyPair c.lift k := ⟨by simpa [Config.lift] using hx.1,
    by simpa [Config.lift] using hx.2, hk, hl⟩
  have hh := (emptyPair_word h k hneq hnn hp).2
  exact hh (closedCoverage n hn c.lift w hw h k)
end ChanLevine.Sem3
