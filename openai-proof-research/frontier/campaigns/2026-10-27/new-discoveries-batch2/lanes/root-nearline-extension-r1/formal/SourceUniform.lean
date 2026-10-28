import Moments

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace KuTorus

theorem line_x {k : ℕ} [NeZero k] (a : ZMod k) :
    line (a,0) (0,1) = Finset.univ.filter (fun z : Board k => z.1 = a) := by
  ext z
  simp [line, Prod.ext_iff, eq_comm]

theorem line_y {k : ℕ} [NeZero k] (a : ZMod k) :
    line (0,a) (1,0) = Finset.univ.filter (fun z : Board k => z.2 = a) := by
  ext z
  simp [line, Prod.ext_iff, eq_comm]

theorem line_sum {k : ℕ} [NeZero k] (a : ZMod k) :
    line (a,0) (-1,1) = Finset.univ.filter (fun z : Board k => z.1+z.2 = a) := by
  ext ⟨x,y⟩
  simp [line, Prod.ext_iff]
  constructor <;> intro h <;> linear_combination -h

theorem line_diff {k : ℕ} [NeZero k] (a : ZMod k) :
    line (a,0) (1,1) = Finset.univ.filter (fun z : Board k => z.1-z.2 = a) := by
  ext ⟨x,y⟩
  simp [line, Prod.ext_iff]
  constructor <;> intro h <;> linear_combination -h

def ExactTwo {k : ℕ} [NeZero k] (A : Finset (Board k)) : Prop :=
  ∀ p v, AllowedDirection v → (A ∩ line p v).card = 2

theorem exactTwo_uniform {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (A : Finset (Board k)) (h : ExactTwo A) : UniformTwo A := by
  have h10 : (1 : ZMod k) ≠ 0 := by
    intro he
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 k).mp (by simpa using he)
    have he' : (k : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd
    omega
  have hf (p v : Board k) (hv : AllowedDirection v)
      (f : Board k → Prop) [DecidablePred f]
      (hl : line p v = Finset.univ.filter f) :
      (A.filter f).card = 2 := by
    have he := h p v hv
    rw [hl] at he
    simpa only [Finset.inter_filter, Finset.inter_univ] using he
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a
  · exact hf (a,0) (0,1) ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
      by intro he; exact h10 (congrArg Prod.snd he)⟩ _ (line_x a)
  · exact hf (0,a) (1,0) ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl),
      by intro he; exact h10 (congrArg Prod.fst he)⟩ _ (line_y a)
  · exact hf (a,0) (-1,1) ⟨Or.inl rfl, Or.inr (Or.inr rfl),
      by intro he; exact h10 (congrArg Prod.snd he)⟩ _ (line_sum a)
  · exact hf (a,0) (1,1) ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr rfl),
      by intro he; exact h10 (congrArg Prod.snd he)⟩ _ (line_diff a)

-- Literal finite-torus statement of Ku Conjecture 5.3.
theorem source_conjecture53 (k : ℕ) [NeZero k] (hk3 : 3 ∣ k)
    (A : Finset (Board k)) : ¬ ExactTwo A := by
  intro h
  have hk : 3 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne k)) hk3
  exact no_uniform_two k hk3 A (exactTwo_uniform hk A h)

end KuTorus
