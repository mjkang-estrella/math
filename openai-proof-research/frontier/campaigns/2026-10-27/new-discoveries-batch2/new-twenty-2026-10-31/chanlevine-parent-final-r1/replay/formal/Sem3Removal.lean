import Sem3Coverage
namespace ChanLevine.Sem3
variable {n : ℕ}

theorem fire_comm {c : SignedConfig n} {a b : ZMod n} (hab : a ≠ b) :
    fire (fire c a) b = fire (fire c b) a := by
  have ht : target (fire c a) b = target c b := by simp [target, fire, Ne.symm hab]
  have ht' : target (fire c b) a = target c a := by simp [target, fire, hab]
  have he : ∀ c d : SignedConfig n, c.x = d.x → c.q = d.q → c = d := by
    rintro ⟨x,q⟩ ⟨y,r⟩ hx hq
    cases hx; cases hq; rfl
  apply he
  · funext k
    change (fire c a).x k - (if k = b then 1 else 0) +
      (if k = target (fire c a) b then 1 else 0) =
      (fire c b).x k - (if k = a then 1 else 0) +
      (if k = target (fire c b) a then 1 else 0)
    rw [ht, ht']
    simp only [fire]
    ring
  · simp only [fire, Function.update_of_ne hab, Function.update_of_ne (Ne.symm hab)]
    exact Function.update_comm hab _ _ _

theorem legal_other {c : SignedConfig n} {a b : ZMod n} (hab : a ≠ b)
    (hb : 0 < c.x b) : 0 < (fire c a).x b := by
  simp only [fire, Ne.symm hab, ite_false, sub_zero]
  split_ifs <;> omega

theorem remove_first {c d : SignedConfig n} {w : List (ZMod n)}
    (h : LegalWord c w d) (a : ZMod n) (ha : a ∈ w) :
    LegalWord (fire c a) (w.erase a) d := by
  induction h with
  | nil => simp at ha
  | @cons c d w b hb hw ih =>
    by_cases he : b = a
    · subst b; simpa using hw
    · have hm : a ∈ w := by simpa [Ne.symm he] using ha
      have hr := ih hm
      rw [fire_comm he] at hr
      simpa [List.erase_cons, Ne.symm he, he] using
        (LegalWord.cons b (legal_other (Ne.symm he) hb) hr)

theorem word_append {c d e : SignedConfig n} {u v : List (ZMod n)}
    (hu : LegalWord c u d) (hv : LegalWord d v e) : LegalWord c (u++v) e := by
  induction hu with
  | nil => exact hv
  | cons a ha _ ih => exact .cons a ha (ih hv)

theorem closed_step {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {c : SignedConfig n} {w : List (ZMod n)} (hw : w ≠ [])
    (h : LegalWord c w c) {a : ZMod n} (ha : 0 < c.x a) :
    Reach (fire c a) c ∧ ∃ v, v ≠ [] ∧ LegalWord (fire c a) v (fire c a) := by
  have hr := remove_first h a (closedCoverage n hn c w hw h a)
  refine ⟨hr.reach, w.erase a ++ [a], ?_, ?_⟩
  · simp
  · exact word_append hr (.cons a ha (.nil _))

theorem closed_reach {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {c d : SignedConfig n} (h : Reach c d)
    (hc : ∃ w, w ≠ [] ∧ LegalWord c w c) :
    Reach d c ∧ ∃ w, w ≠ [] ∧ LegalWord d w d := by
  induction h with
  | refl => exact ⟨.refl, hc⟩
  | tail _ hs ih =>
    obtain ⟨a, ha, rfl⟩ := hs
    obtain ⟨w, hw, hl⟩ := ih.2
    obtain ⟨hr, hp⟩ := closed_step hn hw hl ha
    exact ⟨hr.trans ih.1, hp⟩

theorem closedWordRecurrence : ClosedWordRecurrence := by
  intro n inst hn c w hw h
  refine ⟨?_, ?_⟩
  · cases h with
    | nil => exact False.elim (hw rfl)
    | cons a ha _ => exact ⟨_, a, ha, rfl⟩
  · rintro d ⟨e, hce, hde⟩
    exact hde.trans (closed_reach hn hce ⟨w, hw, h⟩).1
end ChanLevine.Sem3
