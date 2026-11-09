import ChordModel3Orbits
namespace Chord.Model3
open Equiv

/-- Reindexing that preserves orbits preserves their number. -/
theorem orbitCount_equiv {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α ≃ β)
    (h : ∀ x y, Perm.SameCycle f x y ↔ Perm.SameCycle g (e x) (e y)) :
    orbitCount f = orbitCount g :=
  Nat.card_congr (Quotient.congr e h)

/-- Reversing every face traversal does not change the face count. -/
theorem orbitCount_inv {α : Type*} [Fintype α] (f : Perm α) :
    orbitCount f⁻¹ = orbitCount f :=
  orbitCount_equiv _ _ (Equiv.refl _) (fun _ _ => Perm.sameCycle_inv)

theorem orbitCount_conj {α : Type*} [Fintype α] (f e : Perm α) :
    orbitCount (e * f * e⁻¹) = orbitCount f := by
  symm
  apply orbitCount_equiv f _ e
  intro x y
  simp [Perm.sameCycle_conj]

/-- A first-return permutation has one orbit for each ambient orbit it meets.
The hypotheses express orbit correspondence and that every ambient orbit is met. -/
theorem orbitCount_of_section {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (embed : α → β)
    (hcycles : ∀ x y, Perm.SameCycle f x y ↔
      Perm.SameCycle g (embed x) (embed y))
    (hmeets : ∀ y, ∃ x, Perm.SameCycle g (embed x) y) :
    orbitCount f = orbitCount g := by
  let q : Quotient (Perm.SameCycle.setoid f) → Quotient (Perm.SameCycle.setoid g) :=
    Quotient.map embed (fun x y h => (hcycles x y).mp h)
  apply Nat.card_congr (Equiv.ofBijective q ?_)
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        intro h
        apply Quotient.sound
        exact (hcycles x y).mpr (Quotient.exact h)
  · intro y
    induction y using Quotient.inductionOn with
    | _ y =>
      obtain ⟨x,hx⟩ := hmeets y
      exact ⟨Quotient.mk'' x, Quotient.sound hx⟩

/-- Intertwining permutations is sufficient for orbit correspondence. -/
theorem sameCycle_of_intertwine {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α ≃ β) (he : ∀ x, e (f x) = g (e x))
    (x y : α) : Perm.SameCycle f x y ↔ Perm.SameCycle g (e x) (e y) := by
  have hp (k : Nat) (x : α) : e ((f^k) x) = (g^k) (e x) := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [pow_succ', Perm.mul_apply, he] using congrArg g ih
  constructor
  · intro h
    obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
    rw [hp]
    exact (Perm.SameCycle.refl g _).pow_right
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    have hx : (f^k) x = y := e.injective ((hp k x).trans hk)
    rw [← hx]
    exact (Perm.SameCycle.refl f _).pow_right

theorem orbitCount_intertwine {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α ≃ β) (he : ∀ x, e (f x) = g (e x)) :
    orbitCount f = orbitCount g :=
  orbitCount_equiv f g e (sameCycle_of_intertwine f g e he)
end Chord.Model3
