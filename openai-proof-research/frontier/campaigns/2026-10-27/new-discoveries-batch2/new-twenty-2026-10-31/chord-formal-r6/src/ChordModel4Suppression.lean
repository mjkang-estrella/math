import ChordModel3Surgery
import Mathlib.GroupTheory.Perm.Option
namespace Chord.Model4
open Equiv
open Model3

/-- Sending each successor to an orbit step sends every orbit to an orbit. -/
theorem sameCycle_map {α β : Type*} [Finite α] (f : Perm α) (g : Perm β)
    (r : α → β) (hr : ∀ x, Perm.SameCycle g (r x) (r (f x)))
    {x y : α} (h : Perm.SameCycle f x y) : Perm.SameCycle g (r x) (r y) := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact Perm.SameCycle.refl _ _
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hr _)

/-- Suppression of a non-fixed point preserves all orbits. -/
theorem orbitCount_removeNone {α : Type*} [Fintype α] (f : Perm (Option α))
    (hf : f none ≠ none) : orbitCount (removeNone f) = orbitCount f := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, f none = some t := Option.ne_none_iff_exists'.mp hf
  let g := removeNone f
  have hstep (x : α) : Perm.SameCycle f (some x) (some (g x)) := by
    cases hx : f (some x) with
    | none =>
      have hg : some (g x) = some t := (removeNone_none f hx).trans ht
      rw [hg]
      have h1 : Perm.SameCycle f (some x) none := by
        rw [← hx]; exact (Perm.SameCycle.refl f _).apply_right
      have h2 : Perm.SameCycle f none (some t) := by
        rw [← ht]; exact (Perm.SameCycle.refl f _).apply_right
      exact h1.trans h2
    | some y =>
      rw [removeNone_some f ⟨y, hx⟩]
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
        have hg : g x = y := Option.some.inj (removeNone_some f ⟨y, hx⟩ |>.trans hx)
        change Perm.SameCycle g x y
        rw [← hg]; exact (Perm.SameCycle.refl g _).apply_right
  apply orbitCount_of_section g f some
  · intro x y
    constructor
    · exact sameCycle_map g f some hstep
    · intro h; exact sameCycle_map f g r hr h
  · intro y
    cases y with
    | some x => exact ⟨x, Perm.SameCycle.refl _ _⟩
    | none =>
      refine ⟨t, ?_⟩
      rw [← ht]
      exact (Perm.SameCycle.refl f _).apply_left

/-- Adding an isolated point contributes exactly one orbit, even on an empty type. -/
theorem orbitCount_optionCongr {α : Type*} [Fintype α] (g : Perm α) :
    orbitCount g.optionCongr = orbitCount g + 1 := by
  classical
  have hp (k : Nat) (x : Option α) :
      (g.optionCongr ^ k) x = x.map (g ^ k) := by
    induction k with
    | zero => cases x <;> rfl
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, ih]
      cases x <;> simp [optionCongr_apply, pow_succ']
  have hc (x y : α) : Perm.SameCycle g.optionCongr (some x) (some y) ↔
      Perm.SameCycle g x y := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      rw [hp] at hk
      have he := Option.some.inj hk
      rw [← he]; exact (Perm.SameCycle.refl g _).pow_right
    · exact sameCycle_map g g.optionCongr some (fun x => by
        change Perm.SameCycle g.optionCongr (some x) (g.optionCongr (some x))
        exact (Perm.SameCycle.refl _ _).apply_right)
  let enc : Option α → Option (Quotient (Perm.SameCycle.setoid g)) :=
    Option.map (fun x => Quotient.mk'' x)
  have he (x y : Option α) : enc x = enc y ↔ Perm.SameCycle g.optionCongr x y := by
    cases x with
    | none =>
      cases y with
      | none => simp [enc, Perm.SameCycle.refl]
      | some y =>
        simp only [enc, Option.map_none, Option.map_some, reduceCtorEq, false_iff]
        intro h; have := h.eq_of_left (by rfl); contradiction
    | some x =>
      cases y with
      | none =>
        simp only [enc, Option.map_none, Option.map_some, reduceCtorEq, false_iff]
        intro h; have := h.eq_of_right (by rfl); contradiction
      | some y =>
        simp only [enc, Option.map_some, Option.some.injEq]
        exact Quotient.eq_iff_equiv.trans (hc x y).symm
  let q : Quotient (Perm.SameCycle.setoid g.optionCongr) →
      Option (Quotient (Perm.SameCycle.setoid g)) :=
    Quotient.lift enc (fun x y h => (he x y).mpr h)
  have hi : Function.Injective q := by
    intro x y
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        intro h; exact Quotient.sound ((he x y).mp h)
  have hs : Function.Surjective q := by
    intro z
    cases z with
    | none => exact ⟨Quotient.mk'' none, rfl⟩
    | some z =>
      induction z using Quotient.inductionOn with
      | _ x => exact ⟨Quotient.mk'' (some x), rfl⟩
  have hh := Nat.card_congr (Equiv.ofBijective q ⟨hi, hs⟩)
  simpa [orbitCount, Nat.card_eq_fintype_card] using hh
end Chord.Model4
