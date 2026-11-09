import Chord5ErasureSetup
namespace Chord.Round6
open Equiv Model3 Model4

/-- Suppression reflects and preserves connectivity between retained points. -/
theorem sameCycle_removeNone {α : Type*} [Fintype α] (f : Perm (Option α))
    (hf : f none ≠ none) (x y : α) :
    Perm.SameCycle (removeNone f) x y ↔ Perm.SameCycle f (some x) (some y) := by
  obtain ⟨t, ht⟩ : ∃ t, f none = some t := Option.ne_none_iff_exists'.mp hf
  let g := removeNone f
  have he (x : α) : Perm.SameCycle f (some x) (some (g x)) := by
    cases hx : f (some x) with
    | none =>
      rw [show some (g x) = some t from (removeNone_none f hx).trans ht]
      exact ((Perm.SameCycle.refl f (some x)).apply_right.trans
        (by rw [hx, ← ht]; exact (Perm.SameCycle.refl f none).apply_right))
    | some z =>
      rw [removeNone_some f ⟨z, hx⟩]
      exact (Perm.SameCycle.refl f _).apply_right
  let r : Option α → α := fun z => z.getD t
  have hr (z : Option α) : Perm.SameCycle g (r z) (r (f z)) := by
    cases z with
    | none => simp only [r, ht, Option.getD_none, Option.getD_some]; exact Perm.SameCycle.refl _ _
    | some x =>
      cases hx : f (some x) with
      | none =>
        have hg : g x = t := Option.some.inj ((removeNone_none f hx).trans ht)
        change Perm.SameCycle g x t
        rw [← hg]; exact (Perm.SameCycle.refl g _).apply_right
      | some y =>
        have hg : g x = y := Option.some.inj ((removeNone_some f ⟨y,hx⟩).trans hx)
        change Perm.SameCycle g x y
        rw [← hg]; exact (Perm.SameCycle.refl g _).apply_right
  constructor
  · exact sameCycle_map g f some he
  · exact sameCycle_map f g r hr

private theorem inserted_sameCycle {α : Type*} [Fintype α] [DecidableEq α]
    (h : Perm α) (a b : α) :
    Perm.SameCycle (swap none (some a) * h.optionCongr) none (some b) ↔
      Perm.SameCycle h a b := by
  let f := swap none (some a) * h.optionCongr
  have hn : f none ≠ none := by simp [f]
  have he : removeNone f = h := by
    apply optionCongr_injective
    rw [map_equiv_removeNone]
    simp [f]
  have hc := sameCycle_removeNone f hn a b
  rw [he] at hc
  have ha : f none = some a := by simp [f]
  change Perm.SameCycle f none (some b) ↔ Perm.SameCycle h a b
  rw [← Perm.sameCycle_apply_left, ha]
  exact hc.symm

private theorem inserted_count {α : Type*} [Fintype α] [DecidableEq α]
    (h : Perm α) (a : α) :
    orbitCount (swap none (some a) * h.optionCongr) = orbitCount h := by
  have hn : (swap none (some a) * h.optionCongr) none ≠ none := by simp
  have he : removeNone (swap none (some a) * h.optionCongr) = h := by
    apply optionCongr_injective
    rw [map_equiv_removeNone]
    simp
  rw [← orbitCount_removeNone _ hn, he]

private theorem option_swap_refined {α : Type*} [Fintype α] [DecidableEq α]
    (ih : ∀ (h : Perm α) (a b : α), a ≠ b →
      (Perm.SameCycle h a b → orbitCount (h * swap a b) = orbitCount h + 1) ∧
      (¬Perm.SameCycle h a b → orbitCount (h * swap a b) + 1 = orbitCount h))
    (f : Perm (Option α)) (b : α) :
    (Perm.SameCycle f none (some b) → orbitCount (f * swap none (some b)) = orbitCount f + 1) ∧
    (¬Perm.SameCycle f none (some b) → orbitCount (f * swap none (some b)) + 1 = orbitCount f) := by
  let h := removeNone f
  have hf : f = swap none (f none) * h.optionCongr := by
    rw [show h.optionCongr = swap none (f none) * f from map_equiv_removeNone f]
    simp [← mul_assoc]
  have hs : h.optionCongr * swap none (some b) = swap none (some (h b)) * h.optionCongr := by
    rw [mul_swap_eq_swap_mul]; simp
  cases ha : f none with
  | none =>
    have he : f = h.optionCongr := by
      rw [ha, swap_self] at hf
      change f = (1 : Perm (Option α)) * h.optionCongr at hf
      simpa only [one_mul] using hf
    have hn : ¬Perm.SameCycle f none (some b) := by
      intro hc
      have hh := hc.eq_of_left ha
      cases hh
    constructor
    · exact fun hc => False.elim (hn hc)
    · intro _; rw [he, hs, inserted_count, orbitCount_optionCongr]
  | some a =>
    have he : f = swap none (some a) * h.optionCongr := by simpa [ha] using hf
    have hc : Perm.SameCycle f none (some b) ↔ Perm.SameCycle h a b := by
      rw [he]; exact inserted_sameCycle h a b
    have hcount : orbitCount f = orbitCount h := by rw [he, inserted_count]
    have hexpand : f * swap none (some b) =
        swap none (some a) * swap none (some (h b)) * h.optionCongr := by
      rw [he, mul_assoc, hs, ← mul_assoc]
    by_cases hab : h b = a
    · have hy : Perm.SameCycle h a b := by
        rw [← hab]; exact (Perm.SameCycle.refl h b).apply_left
      have hh : orbitCount (f * swap none (some b)) = orbitCount f + 1 := by
        rw [hexpand, hab, swap_mul_self, one_mul, orbitCount_optionCongr, hcount]
      exact ⟨fun _ => hh, fun hn => False.elim (hn (hc.mpr hy))⟩
    · have hx : swap none (some a) * swap none (some (h b)) * h.optionCongr =
          swap none (some (h b)) * (swap (some a) (some (h b)) * h.optionCongr) := by
        have ht : swap none (some (h b)) * swap none (some a) *
            swap none (some (h b)) = swap (some a) (some (h b)) := by
          have hh := (swap_apply_apply (swap none (some (h b))) none (some a)).symm
          simpa [swap_apply_of_ne_of_ne (by simp : some a ≠ none)
            (by simpa using Ne.symm hab : (some a : Option α) ≠ some (h b)), swap_comm] using hh
        rw [← ht]; simp [mul_assoc]
      have hm : optionCongr (swap a (h b)) * h.optionCongr = (h.trans (swap a (h b))).optionCongr := by
        ext x; cases x <;> rfl
      have ht : h.trans (swap a (h b)) = h * swap (h.symm a) b := by
        change swap a (h b) * h = _
        rw [mul_swap_eq_swap_mul]; simp
      have htotal : orbitCount (f * swap none (some b)) = orbitCount (h * swap (h.symm a) b) := by
        rw [hexpand, hx, ← optionCongr_swap, hm, inserted_count, ht]
      have hn : h.symm a ≠ b := by
        intro hh; apply hab; rw [← hh]; exact h.apply_symm_apply a
      have hi := ih h (h.symm a) b hn
      have hrel : Perm.SameCycle h (h.symm a) b ↔ Perm.SameCycle h a b := by
        exact Perm.sameCycle_symm_apply_left
      rw [htotal, hcount]
      exact ⟨fun hh => hi.1 (hrel.mpr (hc.mp hh)),
        fun hh => hi.2 (fun hr => hh (hc.mpr (hrel.mp hr)))⟩

/-- The successor swap splits a single orbit and merges two distinct orbits. -/
theorem swap_orbitCount_refined (size : Nat) (f : Perm (Fin size))
    (a b : Fin size) (hab : a ≠ b) :
    (Perm.SameCycle f a b → orbitCount (f * swap a b) = orbitCount f + 1) ∧
    (¬Perm.SameCycle f a b → orbitCount (f * swap a b) + 1 = orbitCount f) := by
  classical
  induction size with
  | zero => exact Fin.elim0 a
  | succ size ih =>
    let e := finSuccEquiv' a
    let g : Perm (Option (Fin size)) := (e.symm.trans f).trans e
    have hb : e b ≠ none := fun hh => hab ((finSuccEquiv'_eq_none).mp hh)
    obtain ⟨b', hb'⟩ : ∃ b', e b = some b' := Option.ne_none_iff_exists'.mp hb
    have hf : orbitCount f = orbitCount g := orbitCount_intertwine f g e (fun x => by simp [g])
    have hg : orbitCount (f * swap a b) = orbitCount (g * swap none (some b')) := by
      apply orbitCount_intertwine _ _ e
      intro x
      change e (f (swap a b x)) = g (swap none (some b') (e x))
      have ht : e (swap a b x) = swap none (some b') (e x) := by
        by_cases hxa : x = a
        · subst x; simp [e, ← hb']
        · by_cases hxb : x = b
          · subst x; simp [e, ← hb']
          · rw [swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne]
            · exact fun h => hxa (e.injective (h.trans (finSuccEquiv'_at a).symm))
            · exact fun h => hxb (e.injective (h.trans hb'.symm))
      rw [← ht]; simp [g]
    have hc : Perm.SameCycle f a b ↔ Perm.SameCycle g none (some b') := by
      have hh := sameCycle_of_intertwine f g e (fun x => by simp [g]) a b
      simpa only [show e a = none from finSuccEquiv'_at a, hb'] using hh
    rw [hg, hf]
    have hi := option_swap_refined ih g b'
    exact ⟨fun hh => hi.1 (hc.mp hh), fun hh => hi.2 (fun h => hh (hc.mpr h))⟩

/-- The sign of the change is equivalent to the connectivity test. -/
theorem swap_split_iff (size : Nat) (f : Perm (Fin size))
    (a b : Fin size) (hab : a ≠ b) :
    orbitCount (f * swap a b) = orbitCount f + 1 ↔ Perm.SameCycle f a b := by
  have hs := swap_orbitCount_refined size f a b hab
  constructor
  · intro hh
    by_contra hn
    have hm := hs.2 hn
    omega
  · exact hs.1

/-- A successor swap toggles connectivity of its two attachment points. -/
theorem swap_sameCycle_iff (size : Nat) (f : Perm (Fin size))
    (a b : Fin size) (hab : a ≠ b) :
    Perm.SameCycle (f * swap a b) a b ↔ ¬Perm.SameCycle f a b := by
  have hs := swap_orbitCount_refined size f a b hab
  have ht := swap_orbitCount_refined size (f * swap a b) a b hab
  have he : f * swap a b * swap a b = f := by simp [mul_assoc]
  rw [he] at ht
  constructor
  · intro hh hn
    have h1 := ht.1 hh
    have h2 := hs.1 hn
    omega
  · intro hn
    by_contra hh
    have h1 := ht.2 hh
    have h2 := hs.2 hn
    omega

#print axioms sameCycle_removeNone
#print axioms swap_orbitCount_refined
end Chord.Round6
