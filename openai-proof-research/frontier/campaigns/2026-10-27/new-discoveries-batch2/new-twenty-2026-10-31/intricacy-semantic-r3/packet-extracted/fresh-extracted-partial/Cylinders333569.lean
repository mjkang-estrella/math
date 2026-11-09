import Algebra333569

namespace MathDB333569
noncomputable section

theorem trans_sum (z : ℝ × ℝ) (a : Fin 2) : ∑ b : Fin 2, trans z a b = 1 := by
  fin_cases a <;> simp [Fin.sum_univ_two, trans]

theorem stationary_sum {z : ℝ × ℝ} (hz : z ∈ interior) :
    (∑ a : Fin 2, stationary z a) = 1 := by
  have hd : 2-z.1-z.2 ≠ 0 := by
    rcases hz with ⟨_, hu, _, hv⟩
    linarith
  simp [Fin.sum_univ_two, stationary]
  field_simp
  ring

theorem stationary_invariant {z : ℝ × ℝ} (hz : z ∈ interior) (b : Fin 2) :
    (∑ a : Fin 2, stationary z a * trans z a b) = stationary z b := by
  have hd : 2-z.1-z.2 ≠ 0 := by
    rcases hz with ⟨_, hu, _, hv⟩
    linarith
  fin_cases b <;> simp [Fin.sum_univ_two, stationary, trans] <;> field_simp <;> ring

/-- One-step extension of a consecutive cylinder at its right endpoint. -/
theorem wordProb_snoc (z : ℝ × ℝ) (n : ℕ) (w : Fin (n+1) → Fin 2) (b : Fin 2) :
    wordProb z (n+1) (Fin.snoc (α := fun _ : Fin (n+2) => Fin 2) w b) = wordProb z n w * trans z (w (Fin.last n)) b := by
  unfold wordProb
  rw [Fin.prod_univ_castSucc]
  have h0 : Fin.snoc (α := fun _ : Fin (n+2) => Fin 2) w b 0 = w 0 := by
    simp
  rw [h0]
  simp only [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
  have hh : (∏ i : Fin n, trans z (w i.castSucc) (Fin.snoc (α := fun _ : Fin (n+2) => Fin 2) w b i.castSucc.succ)) =
      ∏ i : Fin n, trans z (w i.castSucc) (w i.succ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]
  rw [hh]
  ring

theorem wordProb_right_consistent (z : ℝ × ℝ) (n : ℕ) (w : Fin (n+1) → Fin 2) :
    (∑ b : Fin 2, wordProb z (n+1) (Fin.snoc (α := fun _ : Fin (n+2) => Fin 2) w b)) = wordProb z n w := by
  simp_rw [wordProb_snoc]
  rw [← Finset.mul_sum, trans_sum, mul_one]

/-- Split a finite word into its prefix and its last symbol. -/
def snocEquiv (n : ℕ) : ((Fin (n+1) → Fin 2) × Fin 2) ≃ (Fin (n+2) → Fin 2) where
  toFun v := Fin.snoc v.1 v.2
  invFun w := (fun i => w i.castSucc, w (Fin.last (n+1)))
  left_inv v := by simp
  right_inv w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def oneWordEquiv : Fin 2 ≃ (Fin 1 → Fin 2) where
  toFun a := fun _ => a
  invFun w := w 0
  left_inv _ := rfl
  right_inv w := by funext i; fin_cases i; rfl

/-- Finite consecutive-cylinder weights really are normalized distributions. -/
theorem wordProb_sum {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ) :
    (∑ w : Fin (n+1) → Fin 2, wordProb z n w) = 1 := by
  induction n with
  | zero =>
    rw [← Fintype.sum_equiv oneWordEquiv
      (fun a => stationary z a) (wordProb z 0) (by intro a; simp [oneWordEquiv, wordProb])]
    exact stationary_sum hz
  | succ n ih =>
    rw [← Fintype.sum_equiv (snocEquiv n)
      (fun v => wordProb z (n+1) (Fin.snoc v.1 v.2)) (wordProb z (n+1)) (by intro v; rfl)]
    rw [Fintype.sum_prod_type]
    simp_rw [wordProb_right_consistent]
    exact ih

theorem marginal_nonneg {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ)
    (S : Finset (Fin (n+1))) (a : S → Fin 2) : 0 ≤ marginal z n S a := by
  classical
  unfold marginal
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact le_of_lt (wordProb_pos hz n w)
  · exact le_rfl

theorem marginal_sum {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ)
    (S : Finset (Fin (n+1))) : (∑ a : S → Fin 2, marginal z n S a) = 1 := by
  classical
  have he (w : Fin (n+1) → Fin 2) (a : S → Fin 2) :
      (∀ i : S, w i.val = a i) ↔ a = (fun i : S => w i.val) := by
    constructor
    · intro h; funext i; exact (h i).symm
    · intro h; subst a; intro i; rfl
  unfold marginal
  simp_rw [he]
  rw [Finset.sum_comm]
  simpa using wordProb_sum hz n

theorem marginal_pos {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ)
    (S : Finset (Fin (n+1))) (a : S → Fin 2) : 0 < marginal z n S a := by
  classical
  let w : Fin (n+1) → Fin 2 := fun i => if hi : i ∈ S then a ⟨i, hi⟩ else 0
  have hw : ∀ i : S, w i.val = a i := by intro i; simp [w, i.property]
  have hle : wordProb z n w ≤ marginal z n S a := by
    unfold marginal
    have hh := Finset.single_le_sum
      (f := fun v : Fin (n+1) → Fin 2 => if ∀ i : S, v i.val = a i then wordProb z n v else 0)
      (s := Finset.univ) (a := w)
      (by intro v _; split_ifs; exact le_of_lt (wordProb_pos hz n v); exact le_rfl)
      (Finset.mem_univ w)
    simpa [hw] using hh
  exact lt_of_lt_of_le (wordProb_pos hz n w) hle

theorem marginal_empty {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ)
    (a : (∅ : Finset (Fin (n+1))) → Fin 2) : marginal z n ∅ a = 1 := by
  classical
  unfold marginal
  simpa using wordProb_sum hz n

theorem sampleEntropy_empty {z : ℝ × ℝ} (hz : z ∈ interior) (n : ℕ) :
    sampleEntropy z n ∅ = 0 := by
  classical
  unfold sampleEntropy
  simp_rw [marginal_empty hz n, Real.log_one, mul_zero]
  simp

#print axioms marginal_pos
#print axioms marginal_empty
#print axioms sampleEntropy_empty
#print axioms marginal_nonneg
#print axioms marginal_sum
#print axioms wordProb_sum
#print axioms stationary_sum
#print axioms stationary_invariant
#print axioms wordProb_snoc
#print axioms wordProb_right_consistent
end
end MathDB333569
