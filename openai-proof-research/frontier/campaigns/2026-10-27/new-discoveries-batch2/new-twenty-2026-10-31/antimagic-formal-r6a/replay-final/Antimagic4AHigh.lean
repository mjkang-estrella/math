import AntimagicFinal3
namespace Antimagic.Round4A
open Round3

/-- The ordinary tuples, with the common low-label offset removed. -/
def highEntry (s a j : ℕ) : ℕ :=
  if j < 2 * s - 2 then
    if j % 2 = 0 then (j / 2) * (2 * s - 1) + a + 1
    else (2 * s - 1 - j / 2) * (2 * s - 1) + (2 * s - 1 - a)
  else (s - 1) * (2 * s - 1) + middleEntry (s - 1) a (j - (2 * s - 2))

/-- Unique mixed-radix coordinates for a positive block entry. -/
theorem block_unique (q b c x y : ℕ) (hx : 1 ≤ x ∧ x ≤ q)
    (hy : 1 ≤ y ∧ y ≤ q) (he : b * q + x = c * q + y) : b = c ∧ x = y := by
  have hb : b ≤ c := by
    by_contra h
    have hbc : c + 1 ≤ b := by omega
    have := Nat.mul_le_mul_right q hbc
    nlinarith
  have hc : c ≤ b := by
    by_contra h
    have hbc : b + 1 ≤ c := by omega
    have := Nat.mul_le_mul_right q hbc
    nlinarith
  have h : b = c := by omega
  exact ⟨h, by simpa only [h, Nat.add_left_cancel_iff] using he⟩

/-- Outer entries occupy the bottom and top runs; middle entries fill the gap. -/
theorem highEntry_bands (s a j : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1)
    (hj : j < 2 * s) :
    if j < 2 * s - 2 then
      if j % 2 = 0 then
        1 ≤ highEntry s a j ∧ highEntry s a j ≤ (s - 1) * (2 * s - 1)
      else (s + 1) * (2 * s - 1) < highEntry s a j ∧
        highEntry s a j ≤ (2 * s) * (2 * s - 1)
    else (s - 1) * (2 * s - 1) < highEntry s a j ∧
      highEntry s a j ≤ (s + 1) * (2 * s - 1) := by
  have hq : 0 < 2 * s - 1 := by omega
  have hqa : 2 * s - 1 - a + a = 2 * s - 1 := by omega
  unfold highEntry
  split_ifs with hjo hpar
  · have hdiv : j / 2 + 1 ≤ s - 1 := by omega
    have := Nat.mul_le_mul_right (2 * s - 1) hdiv
    constructor
    · omega
    · nlinarith
  · have hdiv : s + 1 ≤ 2 * s - 1 - j / 2 := by omega
    have hlo := Nat.mul_le_mul_right (2 * s - 1) hdiv
    have hhi := Nat.mul_le_mul_right (2 * s - 1)
      (show 2 * s - 1 - j / 2 + 1 ≤ 2 * s by omega)
    constructor
    · omega
    · nlinarith
  · have hm := middleEntry_range (s - 1) a (j - (2 * s - 2)) (by omega) (by omega)
    have he : (s - 1) * (2 * s - 1) + (4 * (s - 1) + 2) =
        (s + 1) * (2 * s - 1) := by
      have hsub : s - 1 + 1 = s := by omega
      have hsub2 : 2 * s - 1 + 1 = 2 * s := by omega
      nlinarith
    constructor <;> omega

theorem highEntry_range (s a j : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1)
    (hj : j < 2 * s) : 1 ≤ highEntry s a j ∧ highEntry s a j ≤ (2 * s) * (2 * s - 1) := by
  have h := highEntry_bands s a j hs ha hj
  have h1 := Nat.mul_le_mul_right (2 * s - 1) (show s - 1 ≤ 2 * s by omega)
  have h2 := Nat.mul_le_mul_right (2 * s - 1) (show s + 1 ≤ 2 * s by omega)
  split_ifs at h <;> omega

theorem highEntry_injective (s : ℕ) (hs : 2 ≤ s) :
    Function.Injective (fun p : Fin (2 * s - 1) × Fin (2 * s) => highEntry s p.1.val p.2.val) := by
  rintro ⟨a,j⟩ ⟨b,l⟩ he
  change highEntry s a.val j.val = highEntry s b.val l.val at he
  have ha := a.isLt
  have hb := b.isLt
  have hj := j.isLt
  have hl := l.isLt
  have hja := highEntry_bands s a.val j.val hs ha hj
  have hlb := highEntry_bands s b.val l.val hs hb hl
  have horder := Nat.mul_le_mul_right (2 * s - 1) (show s - 1 ≤ s + 1 by omega)
  have hab : a.val = b.val ∧ j.val = l.val := by
    by_cases hjo : j.val < 2 * s - 2 <;> by_cases hlo : l.val < 2 * s - 2
    · by_cases hjp : j.val % 2 = 0 <;> by_cases hlp : l.val % 2 = 0
      · simp only [highEntry, hjo, hlo, hjp, hlp, ite_true] at he
        have h := block_unique (2 * s - 1) _ _ (a.val + 1) (b.val + 1)
          (by omega) (by omega) he
        omega
      · simp only [hjo, hlo, hjp, hlp, ite_true, ite_false] at hja hlb
        omega
      · simp only [hjo, hlo, hjp, hlp, ite_true, ite_false] at hja hlb
        omega
      · simp only [highEntry, hjo, hlo, hjp, hlp, ite_true, ite_false] at he
        have h := block_unique (2 * s - 1) _ _ (2 * s - 1 - a.val) (2 * s - 1 - b.val)
          (by omega) (by omega) he
        omega
    · simp only [hjo, hlo, ite_true, ite_false] at hja hlb
      split_ifs at hja <;> omega
    · simp only [hjo, hlo, ite_true, ite_false] at hja hlb
      split_ifs at hlb <;> omega
    · simp only [highEntry, hjo, hlo, ite_false, Nat.add_left_cancel_iff] at he
      have h := middleEntry_injective (s - 1)
        (a₁ := (⟨a.val, by omega⟩, ⟨j.val - (2 * s - 2), by omega⟩))
        (a₂ := (⟨b.val, by omega⟩, ⟨l.val - (2 * s - 2), by omega⟩)) he
      have h1 := congrArg (fun p => p.1.val) h
      have h2 := congrArg (fun p => p.2.val) h
      dsimp at h1 h2
      omega
  exact Prod.ext (Fin.ext hab.1) (Fin.ext hab.2)

def highMap (s : ℕ) (hs : 2 ≤ s) (p : Fin (2 * s - 1) × Fin (2 * s)) :
    Fin ((2 * s) * (2 * s - 1)) :=
  ⟨highEntry s p.1.val p.2.val - 1,
    by have := highEntry_range s p.1.val p.2.val hs p.1.isLt p.2.isLt; omega⟩

theorem highMap_bijective (s : ℕ) (hs : 2 ≤ s) : Function.Bijective (highMap s hs) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q h
    apply highEntry_injective s hs
    change highEntry s p.1.val p.2.val = highEntry s q.1.val q.2.val
    have hp := highEntry_range s p.1.val p.2.val hs p.1.isLt p.2.isLt
    have hq := highEntry_range s q.1.val q.2.val hs q.1.isLt q.2.isLt
    have he := congrArg Fin.val h
    change highEntry s p.1.val p.2.val - 1 = highEntry s q.1.val q.2.val - 1 at he
    omega
  · simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]


/-- Direct agreement on every ordinary leaf, in the immutable tuple order. -/
theorem highEntry_formula (s a j : ℕ) (hs : 2 ≤ s) (ha : a < 2 * s - 1)
    (hj : j < 2 * s) :
    depthTwoLabel (2 * s) 2 ((2 * s) * (a + 1) + j) = 4 * s + highEntry s a j := by
  by_cases hjo : j < 2 * s - 2
  · have ht : 0 < 2 * s := by omega
    have hd : ((2 * s) * (a + 1) + j) / (2 * s) = a + 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hm : ((2 * s) * (a + 1) + j) % (2 * s) = j := by
      simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hj]
    simp only [depthTwoLabel, highEntry, show ¬ (2 = 1) by decide, ite_false,
      Nat.mul_div_cancel_left s (by decide : 0 < 2), hd, hm,
      show ¬ (a + 1 = 0) by omega, Nat.add_sub_cancel, hjo, ite_true]
    split_ifs <;> omega
  · have hm := depthTwo_middle s a (j - (2 * s - 2)) hs ha (by omega)
    have he : 2 * s - 2 + (j - (2 * s - 2)) = j := by omega
    rw [he] at hm
    simpa only [highEntry, hjo, ite_false, Nat.add_assoc] using hm

/-- Each high label occurs exactly once among the actual ordinary leaf edges. -/
theorem ordinary_label_unique (s x : ℕ) (hs : 2 ≤ s)
    (hx : 4 * s < x ∧ x ≤ 4 * s + (2 * s) * (2 * s - 1)) :
    ∃! p : Fin (2 * s - 1) × Fin (2 * s),
      depthTwoLabel (2 * s) 2 ((2 * s) * (p.1.val + 1) + p.2.val) = x := by
  obtain ⟨p, hp⟩ := (highMap_bijective s hs).2 ⟨x - 4 * s - 1, by omega⟩
  have hr := highEntry_range s p.1.val p.2.val hs p.1.isLt p.2.isLt
  have he := congrArg Fin.val hp
  change highEntry s p.1.val p.2.val - 1 = x - 4 * s - 1 at he
  have hp' : 4 * s + highEntry s p.1.val p.2.val = x := by omega
  refine ⟨p, ?_, ?_⟩
  · dsimp only; rw [highEntry_formula s _ _ hs p.1.isLt p.2.isLt]; exact hp'
  · intro q hq
    rw [highEntry_formula s _ _ hs q.1.isLt q.2.isLt] at hq
    apply highEntry_injective s hs
    change highEntry s q.1.val q.2.val = highEntry s p.1.val p.2.val
    omega

#print axioms highMap_bijective
#print axioms highEntry_formula
#print axioms ordinary_label_unique
end Antimagic.Round4A
