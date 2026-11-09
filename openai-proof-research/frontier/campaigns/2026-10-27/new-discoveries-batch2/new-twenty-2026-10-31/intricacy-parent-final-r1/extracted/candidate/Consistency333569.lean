import Cylinders333569

namespace MathDB333569
noncomputable section

theorem wordProb_cons (z : ℝ × ℝ) (n : ℕ) (w : Fin (n+1) → Fin 2) (a : Fin 2) :
    wordProb z (n+1) (Fin.cons (α := fun _ : Fin (n+2) => Fin 2) a w) =
      stationary z a * trans z a (w 0) *
        ∏ i : Fin n, trans z (w i.castSucc) (w i.succ) := by
  unfold wordProb
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have he : (∏ i : Fin n, trans z (Fin.cons (α := fun _ : Fin (n+2) => Fin 2) a w i.succ.castSucc)
      (w i.succ)) = ∏ i : Fin n, trans z (w i.castSucc) (w i.succ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [show i.succ.castSucc = i.castSucc.succ from rfl]
    simp
  rw [he]
  have h0 : (Fin.castSucc (0 : Fin (n+1))) = (0 : Fin (n+2)) := rfl
  rw [h0, Fin.cons_zero]
  ring

/-- Left endpoint consistency, requiring stationary initial distribution. -/
theorem wordProb_left_consistent {z : ℝ × ℝ} (hz : z ∈ interior)
    (n : ℕ) (w : Fin (n+1) → Fin 2) :
    (∑ a : Fin 2, wordProb z (n+1) (Fin.cons (α := fun _ : Fin (n+2) => Fin 2) a w)) = wordProb z n w := by
  simp_rw [wordProb_cons]
  rw [← Finset.sum_mul, stationary_invariant hz]
  rfl

/-- Arbitrary nested coordinate restrictions within a block are projective. -/
theorem marginal_restrict (z : ℝ × ℝ) (n : ℕ)
    (S T : Finset (Fin (n+1))) (hST : S ⊆ T) (a : S → Fin 2) :
    (∑ b : T → Fin 2, if (∀ i : S, b ⟨i.val, hST i.property⟩ = a i)
      then marginal z n T b else 0) = marginal z n S a := by
  classical
  unfold marginal
  have hh (p : Prop) [Decidable p] (f : (Fin (n+1) → Fin 2) → ℝ) :
      (if p then ∑ w, f w else 0) = ∑ w, if p then f w else 0 := by
    split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have he (b : T → Fin 2) : (∀ i : T, w i.val = b i) ↔ b = (fun i : T => w i.val) := by
    constructor
    · intro h; funext i; exact (h i).symm
    · intro h; subst b; intro i; rfl
  simp_rw [he]
  rw [Finset.sum_eq_single (fun i : T => w i.val)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end
end MathDB333569
