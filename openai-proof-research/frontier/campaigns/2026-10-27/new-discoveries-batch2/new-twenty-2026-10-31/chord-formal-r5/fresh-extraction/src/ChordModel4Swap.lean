import ChordModel4Suppression
import Mathlib.Logic.Equiv.Fin.Basic
namespace Chord.Model4
open Equiv Model3

private theorem inserted_count {α : Type*} [Fintype α] [DecidableEq α]
    (h : Perm α) (a : α) :
    orbitCount (swap none (some a) * h.optionCongr) = orbitCount h := by
  have hn : (swap none (some a) * h.optionCongr) none ≠ none := by simp
  have he : removeNone (swap none (some a) * h.optionCongr) = h := by
    apply optionCongr_injective
    rw [map_equiv_removeNone]
    simp
  rw [← orbitCount_removeNone _ hn, he]

private theorem option_swap {α : Type*} [Fintype α] [DecidableEq α]
    (ih : ∀ (h : Perm α) (a b : α), a ≠ b →
      orbitCount (h * swap a b) = orbitCount h + 1 ∨
      orbitCount (h * swap a b) + 1 = orbitCount h)
    (f : Perm (Option α)) (b : α) :
    orbitCount (f * swap none (some b)) = orbitCount f + 1 ∨
    orbitCount (f * swap none (some b)) + 1 = orbitCount f := by
  let h := removeNone f
  have hf : f = swap none (f none) * h.optionCongr := by
    rw [show h.optionCongr = swap none (f none) * f from map_equiv_removeNone f]
    simp [← mul_assoc]
  have hs : h.optionCongr * swap none (some b) =
      swap none (some (h b)) * h.optionCongr := by
    rw [mul_swap_eq_swap_mul]
    simp
  cases ha : f none with
  | none =>
    have he : f = h.optionCongr := by
      rw [ha, swap_self] at hf
      change f = (1 : Perm (Option α)) * h.optionCongr at hf
      simpa only [one_mul] using hf
    rw [he, hs, inserted_count, orbitCount_optionCongr]
    exact Or.inr rfl
  | some a =>
    have he : f = swap none (some a) * h.optionCongr := by simpa [ha] using hf
    have hc : orbitCount f = orbitCount h := by rw [he, inserted_count]
    rw [hc, he, mul_assoc, hs, ← mul_assoc]
    by_cases hab : h b = a
    · rw [hab, swap_mul_self, one_mul, orbitCount_optionCongr]
      exact Or.inl rfl
    · have hx : swap none (some a) * swap none (some (h b)) * h.optionCongr =
          swap none (some (h b)) * (swap (some a) (some (h b)) * h.optionCongr) := by
        have ht : swap none (some (h b)) * swap none (some a) *
            swap none (some (h b)) = swap (some a) (some (h b)) := by
          have hh := (swap_apply_apply (swap none (some (h b))) none (some a)).symm
          simpa [swap_apply_of_ne_of_ne (by simp : some a ≠ none) (by simpa using Ne.symm hab : (some a : Option α) ≠ some (h b)), swap_comm] using hh
        rw [← ht]
        simp [mul_assoc]
      rw [hx, ← optionCongr_swap]
      have hm : optionCongr (swap a (h b)) * h.optionCongr = (h.trans (swap a (h b))).optionCongr := by
        ext x; cases x <;> rfl
      rw [hm]
      change orbitCount (swap none (some (h b)) * (h.trans (swap a (h b))).optionCongr) = _ ∨ _
      rw [inserted_count]
      have ht : h.trans (swap a (h b)) = h * swap (h.symm a) b := by
        change swap a (h b) * h = _
        rw [mul_swap_eq_swap_mul]
        simp
      rw [ht]
      apply ih h (h.symm a) b
      intro hh
      apply hab
      rw [← hh]
      exact h.apply_symm_apply a

/-- The generic successor-swap law, including all fixed-point cases. -/
theorem swapCycleLaw_proved : SwapCycleLaw := by
  classical
  intro size
  induction size with
  | zero => intro f a; exact Fin.elim0 a
  | succ size ih =>
    intro f a b hab
    let e := finSuccEquiv' a
    let g : Perm (Option (Fin size)) := (e.symm.trans f).trans e
    have hb : e b ≠ none := by
      exact fun hh => hab ((finSuccEquiv'_eq_none).mp hh)
    obtain ⟨b', hb'⟩ : ∃ b', e b = some b' := by
      cases hx : e b with
      | none => exact False.elim (hb hx)
      | some x => exact ⟨x, rfl⟩
    have hf : orbitCount f = orbitCount g :=
      orbitCount_intertwine f g e (fun x => by simp [g])
    have hg : orbitCount (f * swap a b) = orbitCount (g * swap none (some b')) := by
      apply orbitCount_intertwine _ _ e
      intro x
      change e (f (swap a b x)) = g (swap none (some b') (e x))
      have ht : e (swap a b x) = swap none (some b') (e x) := by
        by_cases hxa : x = a
        · subst x; simp [e, ← hb']
        · by_cases hxb : x = b
          · subst x; simp [e, ← hb']
          · rw [swap_apply_of_ne_of_ne hxa hxb]
            rw [swap_apply_of_ne_of_ne]
            · exact fun h => hxa (e.injective (h.trans (finSuccEquiv'_at a).symm))
            · exact fun h => hxb (e.injective (h.trans hb'.symm))
      rw [← ht]
      simp [g]
    rw [hg, hf]
    exact option_swap ih g b'
#print axioms swapCycleLaw_proved
end Chord.Model4
