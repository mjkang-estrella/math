import WheelWeights
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open scoped BigOperators
namespace WheelFormal

theorem cycle_one_ne_zero (t : ℕ) (ht : 1 ≤ t) :
    (1 : ZMod (2*t+1)) ≠ 0 := by
  have hm : 1 < 2*t+1 := by omega
  intro h
  have := congrArg ZMod.val h
  simpa [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hm] using this

theorem cycle_independent_card (t : ℕ) (ht : 1 ≤ t)
    (A : Finset (ZMod (2*t+1)))
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ rimAdj (2*t+1) x y) :
    A.card ≤ t := by
  classical
  let B := A.image (fun x => x+1)
  have hcard : B.card = A.card := Finset.card_image_of_injective _ (add_left_injective 1)
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    have hn : y ≠ y+1 := by
      intro h
      have : (1 : ZMod (2*t+1)) = 0 := by exact (add_left_cancel (show y+1=y+0 by simpa using h.symm))
      exact cycle_one_ne_zero t ht this
    exact hA y hy (y+1) hx hn ⟨hn, Or.inl rfl⟩
  have hc := Finset.card_le_card (Finset.subset_univ (A ∪ B))
  rw [Finset.card_union_of_disjoint hd, hcard] at hc
  simp only [Finset.card_univ, ZMod.card] at hc
  omega

/-- Pair 1 with 2, 3 with 4, ...; leave 0 fixed. -/
def cyclePair (t : ℕ) (x : ZMod (2*t+1)) : ZMod (2*t+1) :=
  if x.val = 0 then 0 else
  if x.val % 2 = 1 then (x.val+1 : ℕ) else (x.val-1 : ℕ)

theorem cyclePair_spec (t : ℕ) (x : ZMod (2*t+1)) :
    (cyclePair t (cyclePair t x) = x) ∧
    (cyclePair t x = x ↔ x = 0) ∧
    (x ≠ 0 → rimAdj (2*t+1) x (cyclePair t x)) := by
  have hv : x.val < 2*t+1 := ZMod.val_lt x
  have castval : (x.val : ZMod (2*t+1)) = x := ZMod.natCast_zmod_val x
  by_cases hz : x.val = 0
  · have hx : x = 0 := by rw [← castval, hz]; rfl
    subst x
    simp [cyclePair, rimAdj]
  · by_cases ho : x.val % 2 = 1
    · have hlt : x.val+1 < 2*t+1 := by omega
      have hpos : x.val+1 ≠ 0 := by omega
      have heven : (x.val+1)%2 ≠ 1 := by omega
      have hp : cyclePair t x = x+1 := by simp [cyclePair, hz, ho, Nat.cast_add, castval]
      have hpv : (cyclePair t x).val = x.val+1 := by
        simp only [cyclePair, hz, ho, ite_false, ite_true, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      have hpp : cyclePair t (cyclePair t x) = x := by
        rw [cyclePair]; simp only [hpv, hpos, heven, ite_false, Nat.add_sub_cancel, castval]
      have hn : x ≠ cyclePair t x := by
        intro h; have hh := congrArg ZMod.val h; rw [hpv] at hh; omega
      exact ⟨hpp, ⟨fun h => (hn h.symm).elim, fun h => by subst x; simp [cyclePair]⟩,
        fun _ => ⟨hn, Or.inl hp⟩⟩
    · have hlt : x.val-1 < 2*t+1 := by omega
      have hpos : x.val-1 ≠ 0 := by omega
      have hodd : (x.val-1)%2 = 1 := by omega
      have hpv : (cyclePair t x).val = x.val-1 := by
        simp only [cyclePair, hz, ho, ite_false, ite_true, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      have hpp : cyclePair t (cyclePair t x) = x := by
        rw [cyclePair]; simp only [hpv, hpos, hodd, ite_false, ite_true, show x.val-1+1=x.val by omega, castval]
      have hp : x = cyclePair t x + 1 := by
        rw [cyclePair]; simp only [hz, ho, ite_false]
        calc
          x = ((x.val-1+1 : ℕ) : ZMod (2*t+1)) := by rw [show x.val-1+1=x.val by omega, castval]
          _ = _ := by push_cast; rfl
      have hn : x ≠ cyclePair t x := by
        intro h; have hh := congrArg ZMod.val h; rw [hpv] at hh; omega
      exact ⟨hpp, ⟨fun h => (hn h.symm).elim, fun h => by subst x; simp [cyclePair]⟩,
        fun _ => ⟨hn, Or.inr hp⟩⟩
end WheelFormal
