import UpperIndexed
set_option autoImplicit false
namespace WheelFormal

/-- Adjacency, including the wrap edge, in natural representatives. -/
theorem rimAdj_val (t : ℕ) (x y : ZMod (2*t+1))
    (h : rimAdj (2*t+1) x y) :
    y.val = x.val+1 ∨ x.val = y.val+1 ∨
    (x.val = 2*t ∧ y.val = 0) ∨ (y.val = 2*t ∧ x.val = 0) := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have step : ∀ a b : ZMod (2*t+1), b = a+1 →
      b.val = a.val+1 ∨ (a.val = 2*t ∧ b.val = 0) := by
    intro a b hab
    have ha := ZMod.val_lt a
    subst b
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    by_cases ht : t = 0
    · subst t
      have az : a = 0 := by
        apply ZMod.val_injective
        simp only [ZMod.val_zero]
        omega
      simp [az]
    · have ho : 1 % (2*t+1) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [ho]
      by_cases hlt : a.val+1 < 2*t+1
      · exact Or.inl (Nat.mod_eq_of_lt hlt)
      · right
        have he : a.val = 2*t := by omega
        simp [he]
  rcases h.2 with h | h
  · rcases step x y h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases step y x h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

def alternating (t : ℕ) (x : ZMod (2*t+1)) : Prop :=
  x.val < 2*t ∧ x.val % 2 = 0

theorem alternating_independent (t : ℕ) (x y : ZMod (2*t+1))
    (hx : alternating t x) (hy : alternating t y) :
    ¬ rimAdj (2*t+1) x y := by
  intro h
  have hv := rimAdj_val t x y h
  unfold alternating at hx hy
  omega

theorem rimAdj_translate (t : ℕ) (a x y : ZMod (2*t+1)) :
    rimAdj (2*t+1) (x-a) (y-a) ↔ rimAdj (2*t+1) x y := by
  simp only [rimAdj]
  constructor <;> rintro ⟨hn, h | h⟩
  · exact ⟨(by intro he; apply hn; linear_combination he), Or.inl (by linear_combination h)⟩
  · exact ⟨(by intro he; apply hn; linear_combination he), Or.inr (by linear_combination h)⟩
  · exact ⟨(by intro he; apply hn; linear_combination he), Or.inl (by linear_combination h)⟩
  · exact ⟨(by intro he; apply hn; linear_combination he), Or.inr (by linear_combination h)⟩

/-- Nondeleted coordinates have opposite parity along each path edge. -/
theorem deleted_parity (t : ℕ) (a x y : ZMod (2*t+1))
    (hx : x ≠ a) (hy : y ≠ a) (h : rimAdj (2*t+1) x y) :
    (x-a-1).val % 2 ≠ (y-a-1).val % 2 := by
  have he : rimAdj (2*t+1) (x-a-1) (y-a-1) := by
    apply (rimAdj_translate t 1 _ _).mpr
    exact (rimAdj_translate t a x y).mpr h
  have hxx : (x-a-1).val ≠ 2*t := by
    intro hh
    have hh' : x-a-1 = (-1 : ZMod (2*t+1)) := by
      rw [← ZMod.natCast_zmod_val (x-a-1), hh]
      have hz : ((2*t+1:ℕ) : ZMod (2*t+1)) = 0 := by simp
      push_cast at hz
      push_cast
      linear_combination hz
    apply hx
    linear_combination hh'
  have hyy : (y-a-1).val ≠ 2*t := by
    intro hh
    have hh' : y-a-1 = (-1 : ZMod (2*t+1)) := by
      rw [← ZMod.natCast_zmod_val (y-a-1), hh]
      have hz : ((2*t+1:ℕ) : ZMod (2*t+1)) = 0 := by simp
      push_cast at hz
      push_cast
      linear_combination hz
    apply hy
    linear_combination hh'
  have hv := rimAdj_val t _ _ he
  omega
end WheelFormal
