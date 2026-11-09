import Cardinality
open scoped BigOperators
namespace ChanLevine
variable {n : ℕ} [NeZero n]

def translate (a : ZMod n) (c : Config n) : Config n :=
  ⟨fun k => c.x (k-a), fun k => c.q (k-a)⟩

omit [NeZero n] in
theorem translate_cancel (a : ZMod n) (c : Config n) :
    translate (-a) (translate a c) = c := by
  cases c
  simp [translate]

omit [NeZero n] in
theorem translate_test (a : ZMod n) (c : Config n) (h : CycleTest c) :
    CycleTest (translate a c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hl
    simpa [translate, sub_add_eq_add_sub] using
      h.1 (k-a) hk (by simpa [translate, sub_add_eq_add_sub] using hl)
  · intro hq
    obtain ⟨k, hk⟩ := h.2.1 (fun k => by simpa [translate] using hq (k+a))
    exact ⟨k+a, by simpa [translate] using hk⟩
  · intro hq
    obtain ⟨k, hk⟩ := h.2.2 (fun k => by simpa [translate] using hq (k+a))
    exact ⟨k+a, by simpa [translate] using hk⟩

theorem translate_level (a : ZMod n) (c : Config n) :
    chipLevel (translate a c) = chipLevel c := by
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
theorem translate_weight (a : ZMod n) (c : Config n) :
    chipWeight (translate a c) = chipWeight c + a * (chipLevel c : ZMod n) := by
  have hx : (∑ k : ZMod n, k * (c.x (k-a) : ZMod n)) =
      ∑ k : ZMod n, (k+a) * (c.x k : ZMod n) := by
    exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun k => by simp)
  have hq : (∑ k : ZMod n, if c.q (k-a) then (0 : ZMod n) else 1) =
      ∑ k : ZMod n, if c.q k then (0 : ZMod n) else 1 :=
    Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  unfold chipWeight weight
  dsimp only [Config.lift, translate]
  simp only [Int.cast_natCast]
  rw [hx, hq]
  simp [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, chipLevel, Nat.cast_sum]
  ring

noncomputable def translateFibre (a : ZMod n) (m : ℕ) (i : ZMod n) :
    {c : Config n // CycleTest c ∧ chipLevel c = m ∧ chipWeight c = i} ≃
    {c : Config n // CycleTest c ∧ chipLevel c = m ∧ chipWeight c = i + a*m} where
  toFun c := ⟨translate a c.val, translate_test a c.val c.property.1,
    (translate_level a c.val).trans c.property.2.1, by
      rw [translate_weight, c.property.2.1, c.property.2.2]⟩
  invFun c := ⟨translate (-a) c.val, translate_test (-a) c.val c.property.1,
    (translate_level (-a) c.val).trans c.property.2.1, by
      rw [translate_weight, c.property.2.1, c.property.2.2]; ring⟩
  left_inv c := Subtype.ext (translate_cancel a c.val)
  right_inv c := Subtype.ext (by simpa using translate_cancel (-a) c.val)

theorem rotationCount_proof : RotationCount := by
  intro n m _ _ _ i
  simpa [testCount] using (Nat.card_congr (translateFibre (1 : ZMod n) m i)).symm
end ChanLevine
