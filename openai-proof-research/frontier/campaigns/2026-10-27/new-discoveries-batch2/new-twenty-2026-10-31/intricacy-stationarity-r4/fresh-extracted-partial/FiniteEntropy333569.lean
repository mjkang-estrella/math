import Stationarity333569
import Entropy333569

namespace MathDB333569
noncomputable section

/-- Finite Shannon chain rule, proved from logarithms and row normalization. -/
theorem entropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (K : A → B → ℝ) (hp : ∀ a, 0 < p a)
    (hK : ∀ a b, 0 < K a b) (hs : ∀ a, ∑ b, K a b = 1) :
    -(∑ a, ∑ b, (p a * K a b) * Real.log (p a * K a b)) =
      -(∑ a, p a * Real.log (p a)) +
        ∑ a, p a * (-(∑ b, K a b * Real.log (K a b))) := by
  simp_rw [Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (hK _ _))]
  have he (a : A) : (∑ b, p a * K a b * (Real.log (p a) + Real.log (K a b))) =
      p a * Real.log (p a) + p a * ∑ b, K a b * Real.log (K a b) := by
    calc
      _ = ∑ b, ((p a * Real.log (p a)) * K a b +
          p a * (K a b * Real.log (K a b))) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, mul_one]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

def rowEntropy (z : ℝ × ℝ) (a : Fin 2) : ℝ :=
  -(∑ b : Fin 2, trans z a b * Real.log (trans z a b))

def wordEntropy (z : ℝ × ℝ) (n : ℕ) : ℝ :=
  -(∑ w : Fin (n+1) → Fin 2, wordProb z n w * Real.log (wordProb z n w))

def initialEntropy (z : ℝ × ℝ) : ℝ :=
  -(∑ a : Fin 2, stationary z a * Real.log (stationary z a))

def transitionEntropy (z : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 2, stationary z a * rowEntropy z a

/-- The finite joint entropy chain rule applied to the exact word distribution. -/
theorem wordEntropy_succ (z : ℝ × ℝ) (hz : z ∈ interior) (n : ℕ) :
    wordEntropy z (n+1) = wordEntropy z n +
      ∑ w : Fin (n+1) → Fin 2, wordProb z n w * rowEntropy z (w (Fin.last n)) := by
  unfold wordEntropy
  rw [← Fintype.sum_equiv (snocEquiv n)
    (fun v => wordProb z (n+1) (Fin.snoc v.1 v.2) *
      Real.log (wordProb z (n+1) (Fin.snoc v.1 v.2)))
    (fun w => wordProb z (n+1) w * Real.log (wordProb z (n+1) w)) (by intro v; rfl)]
  rw [Fintype.sum_prod_type]
  simp_rw [wordProb_snoc]
  exact entropy_chain (wordProb z n) (fun w b => trans z (w (Fin.last n)) b)
    (wordProb_pos hz n) (fun _ _ => trans_pos hz _ _) (fun _ => trans_sum z _)

def consEquiv (n : ℕ) : (Fin 2 × (Fin (n+1) → Fin 2)) ≃ (Fin (n+2) → Fin 2) where
  toFun v := Fin.cons v.1 v.2
  invFun w := (w 0, fun i => w i.succ)
  left_inv v := by simp
  right_inv w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Every endpoint has the stationary law, also in the finite source distribution. -/
theorem wordProb_last_expectation (z : ℝ × ℝ) (hz : z ∈ interior)
    (n : ℕ) (g : Fin 2 → ℝ) :
    (∑ w : Fin (n+1) → Fin 2, wordProb z n w * g (w (Fin.last n))) =
      ∑ a : Fin 2, stationary z a * g a := by
  induction n with
  | zero =>
    rw [← Fintype.sum_equiv oneWordEquiv
      (fun a => stationary z a * g a)
      (fun w => wordProb z 0 w * g (w (Fin.last 0))) (by intro a; simp [oneWordEquiv, wordProb])]
  | succ n ih =>
    rw [← Fintype.sum_equiv (consEquiv n)
      (fun v => wordProb z (n+1) (Fin.cons v.1 v.2) * g (v.2 (Fin.last n)))
      (fun w => wordProb z (n+1) w * g (w (Fin.last (n+1))))
      (by intro v; simp [consEquiv])]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, wordProb_left_consistent hz]
    exact ih

/-- Exact finite block Shannon entropy, before taking any asymptotic limit. -/
theorem wordEntropy_eq (z : ℝ × ℝ) (hz : z ∈ interior) (n : ℕ) :
    wordEntropy z n = initialEntropy z + (n : ℝ) * transitionEntropy z := by
  induction n with
  | zero =>
    unfold wordEntropy initialEntropy
    rw [← Fintype.sum_equiv oneWordEquiv
      (fun a => stationary z a * Real.log (stationary z a))
      (fun w => wordProb z 0 w * Real.log (wordProb z 0 w))
      (by intro a; simp [oneWordEquiv, wordProb])]
    simp
  | succ n ih =>
    rw [wordEntropy_succ z hz, wordProb_last_expectation z hz, ih]
    simp only [transitionEntropy, Nat.cast_add, Nat.cast_one]
    ring

/-- Identify the finite-chain conditional entropy with the source chart function. -/
theorem transitionEntropy_chart {l : ℝ} (hl : l ≠ 1) (t : ℝ) :
    transitionEntropy (chart l t) = conditionalEntropy l t := by
  unfold transitionEntropy rowEntropy
  simp_rw [chart_stationary hl, chart_trans]
  simp only [Fin.sum_univ_two, kernel, pi, conditionalEntropy]
  simp_rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [Real.negMulLog]
  ring_nf

def univWordEquiv (n : ℕ) : (↥(Finset.univ : Finset (Fin (n+1))) → Fin 2) ≃ (Fin (n+1) → Fin 2) where
  toFun a j := a ⟨j,Finset.mem_univ j⟩
  invFun w j := w j.val
  left_inv a := by rfl
  right_inv w := by rfl

theorem marginal_univ (z : ℝ × ℝ) (n : ℕ)
    (a : ↥(Finset.univ : Finset (Fin (n+1))) → Fin 2) :
    marginal z n Finset.univ a = wordProb z n (univWordEquiv n a) := by
  classical
  unfold marginal
  have he (w : Fin (n+1) → Fin 2) :
      (∀ i : ↥(Finset.univ : Finset (Fin (n+1))), w i.val = a i) ↔ w = univWordEquiv n a := by
    constructor
    · intro h; funext j; exact h ⟨j, Finset.mem_univ j⟩
    · intro h; subst w; intro i; rfl
  simp_rw [he]
  simp

theorem sampleEntropy_univ (z : ℝ × ℝ) (n : ℕ) :
    sampleEntropy z n Finset.univ = wordEntropy z n := by
  classical
  unfold sampleEntropy wordEntropy
  simp_rw [marginal_univ]
  congr 1
  exact Fintype.sum_equiv (univWordEquiv n) _ _ (fun _ => rfl)

/-- The actual rank-zero block entropy is H(pi) + n H(P). -/
theorem rankZero_blockEntropy (z : ℝ × ℝ) (hz : z ∈ interior) (k : ℤ) (n : ℕ) :
    rankZeroSampleEntropy (twoSidedLaw z hz) k n Finset.univ =
      initialEntropy z + (n : ℝ) * transitionEntropy z := by
  rw [rankZeroSampleEntropy_eq z hz, sampleEntropy_univ, wordEntropy_eq z hz]

theorem rankZero_blockEntropy_chart {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (k : ℤ) (n : ℕ) :
    rankZeroSampleEntropy (twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1))
      k n Finset.univ = initialEntropy (chart l t) + (n : ℝ) * conditionalEntropy l t := by
  rw [rankZero_blockEntropy, transitionEntropy_chart (ne_of_lt hl1)]

end
end MathDB333569
