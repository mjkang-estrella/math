import Data
namespace Hetyei347230
theorem toPoly_cons (p : Word × ℤ) (l : FSum) :
    toPoly (p :: l) = Finsupp.single p.1 (p.2 : ℚ) + toPoly l := by
  simp [toPoly]
theorem toPoly_append (l m : FSum) : toPoly (l ++ m) = toPoly l + toPoly m := by
  simp [toPoly]
theorem toPoly_scale (l : FSum) (c : ℤ) :
    toPoly (l.map fun q => (q.1, c * q.2)) = (c : ℚ) • toPoly l := by
  induction l with
  | nil => simp [toPoly]
  | cons p l ih => simp [toPoly_cons, ih, smul_add, Finsupp.smul_single]
theorem I2_toPoly (l : FSum) : I2 (toPoly l) = toPoly (I2L l) := by
  induction l with
  | nil => simp [toPoly, I2L]
  | cons p l ih =>
    simp only [toPoly_cons, map_add, I2L, List.flatMap_cons, toPoly_append]
    rw [toPoly_scale, ih]
    simp [I2, I2L]
theorem toPoly_coeff (l : FSum) (w : Word) :
    toPoly l w = (coeffL l w : ℚ) := by
  induction l with
  | nil => simp [toPoly, coeffL]
  | cons p l ih =>
    by_cases hp : p.1 = w
    · simp [toPoly_cons, coeffL, hp, ih]
    · simp [toPoly_cons, coeffL, hp, ih]
theorem allWords_complete (w : Word) : w ∈ allWords w.length := by
  induction w with
  | nil => simp [allWords_zero]
  | cons b w ih =>
    simp only [List.length_cons, allWords_succ, List.mem_flatMap]
    exact ⟨w, ih, by cases b <;> simp⟩
theorem toPoly_eq_zero_of_coeff (l : FSum) (S : List Word) (hS : ∀ p ∈ l, p.1 ∈ S)
    (h : ∀ w ∈ S, coeffL l w = 0) : toPoly l = 0 := by
  ext w
  rw [toPoly_coeff]
  by_cases hw : w ∈ S
  · simp [h w hw]
  · have hz : coeffL l w = 0 := by
      unfold coeffL
      have : l.filter (fun p => p.1 == w) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro p hp
        simp only [beq_iff_eq]
        intro he
        exact hw (he ▸ hS p hp)
      simp [this]
    simp [hz]
end Hetyei347230
