import Selected333569

namespace MathDB333569
noncomputable section

/-- Inhomogeneous stationary binary path; each edge may have a different gap. -/
def selectedProb (t : ℝ) (d : ℕ) (r : Fin d → ℝ) (a : Fin (d+1) → Fin 2) : ℝ :=
  pi t (a 0) * ∏ j : Fin d, kernel (r j) t (a j.castSucc) (a j.succ)

theorem selectedProb_pos {t : ℝ} (ht : -1 < t) (ht1 : t < 1)
    (d : ℕ) (r : Fin d → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1)
    (a : Fin (d+1) → Fin 2) : 0 < selectedProb t d r a := by
  apply mul_pos
  · unfold pi; split_ifs <;> linarith
  · exact Finset.prod_pos (fun j _ => kernel_pos (hr j).1 (hr j).2 ht ht1 _ _)

theorem selectedProb_snoc (t : ℝ) (d : ℕ) (r : Fin (d+1) → ℝ)
    (a : Fin (d+1) → Fin 2) (b : Fin 2) :
    selectedProb t (d+1) r (Fin.snoc a b) =
      selectedProb t d (fun j => r j.castSucc) a * kernel (r (Fin.last d)) t (a (Fin.last d)) b := by
  unfold selectedProb
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_castSucc, Fin.succ_last]
  have h0 : (0 : Fin (d+2)) = (0 : Fin (d+1)).castSucc := rfl
  rw [h0, Fin.snoc_castSucc]
  ring

/-- All selected endpoints retain pi, even with different edge kernels. -/
theorem selectedProb_last_expectation (t : ℝ) (d : ℕ) (r : Fin d → ℝ)
    (f : Fin 2 → ℝ) :
    (∑ a : Fin (d+1) → Fin 2, selectedProb t d r a * f (a (Fin.last d))) =
      ∑ b : Fin 2, pi t b * f b := by
  induction d generalizing f with
  | zero =>
    rw [← Fintype.sum_equiv oneWordEquiv
      (fun b => pi t b * f b) _ (by intro b; simp [selectedProb, oneWordEquiv])]
  | succ d ih =>
    rw [← Fintype.sum_equiv (snocEquiv d)
      (fun v => selectedProb t (d+1) r (Fin.snoc v.1 v.2) * f v.2) _
      (by intro v; simp [snocEquiv])]
    rw [Fintype.sum_prod_type]
    simp_rw [selectedProb_snoc, mul_assoc, ← Finset.mul_sum]
    rw [ih _ (fun b => ∑ i : Fin 2, kernel (r (Fin.last d)) t b i * f i)]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, pi_invariant]

def selectedEntropy (t : ℝ) (d : ℕ) (r : Fin d → ℝ) : ℝ :=
  -(∑ a : Fin (d+1) → Fin 2, selectedProb t d r a * Real.log (selectedProb t d r a))

theorem kernel_entropy {r : ℝ} (hr : r ≠ 1) (t : ℝ) :
    (∑ a : Fin 2, pi t a * (-(∑ b : Fin 2, kernel r t a b * Real.log (kernel r t a b)))) =
      conditionalEntropy r t := by
  have h := transitionEntropy_chart hr t
  unfold transitionEntropy rowEntropy at h
  simpa only [chart_stationary hr, chart_trans] using h

/-- Entropy of every positive inhomogeneous selected chain. -/
theorem selectedEntropy_eq {t : ℝ} (ht : -1 < t) (ht1 : t < 1)
    (d : ℕ) (r : Fin d → ℝ) (hr : ∀ j, 0 < r j ∧ r j < 1) :
    selectedEntropy t d r = -(∑ a : Fin 2, pi t a * Real.log (pi t a)) +
      ∑ j : Fin d, conditionalEntropy (r j) t := by
  induction d with
  | zero =>
    unfold selectedEntropy
    rw [← Fintype.sum_equiv oneWordEquiv
      (fun a => pi t a * Real.log (pi t a)) _
      (by intro a; simp [selectedProb, oneWordEquiv])]
    simp
  | succ d ih =>
    have hrec : selectedEntropy t (d+1) r = selectedEntropy t d (fun j => r j.castSucc) +
        ∑ a : Fin (d+1) → Fin 2, selectedProb t d (fun j => r j.castSucc) a *
          (-(∑ b : Fin 2, kernel (r (Fin.last d)) t (a (Fin.last d)) b *
            Real.log (kernel (r (Fin.last d)) t (a (Fin.last d)) b))) := by
      unfold selectedEntropy
      rw [← Fintype.sum_equiv (snocEquiv d)
        (fun v => selectedProb t (d+1) r (Fin.snoc v.1 v.2) *
          Real.log (selectedProb t (d+1) r (Fin.snoc v.1 v.2))) _ (by intro v; rfl)]
      rw [Fintype.sum_prod_type]
      simp_rw [selectedProb_snoc]
      exact entropy_chain _ _ (selectedProb_pos ht ht1 d _ (fun j => hr j.castSucc))
        (fun _ _ => kernel_pos (hr _).1 (hr _).2 ht ht1 _ _) (fun _ => kernel_sum _ _ _)
    rw [hrec, selectedProb_last_expectation t d (fun j => r j.castSucc)
      (fun a => -(∑ b : Fin 2, kernel (r (Fin.last d)) t a b * Real.log (kernel (r (Fin.last d)) t a b))),
      kernel_entropy (ne_of_lt (hr _).2),
      ih _ (fun j => hr j.castSucc),
      Fin.sum_univ_castSucc (fun j : Fin (d+1) => conditionalEntropy (r j) t)]
    ring


open MeasureTheory
/-- Actual entropy of a specified finite list of coordinate observations. -/
def observedEntropy (μ : Measure (ℤ → Fin 2)) (m : ℕ) (s : Fin m → ℤ) : ℝ :=
  -(∑ a : Fin m → Fin 2, (μ {x | ∀ j, x (s j) = a j}).toReal *
    Real.log ((μ {x | ∀ j, x (s j) = a j}).toReal))

theorem observedEntropy_empty (μ : Measure (ℤ → Fin 2)) [IsProbabilityMeasure μ]
    (s : Fin 0 → ℤ) : observedEntropy μ 0 s = 0 := by
  simp [observedEntropy]

/-- Selected entropy H(pi) plus the consecutive gap conditional entropies,
for the actual countably additive two-sided law, including singleton lists. -/
theorem observedEntropy_selected {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (d : ℕ)
    (s : Fin (d+1) → ℤ) (hs : StrictMono s) :
    observedEntropy (twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)) (d+1) s =
      initialEntropy (chart l t) +
      ∑ j : Fin d, conditionalEntropy (l ^ (s j.succ - s j.castSucc).toNat) t := by
  let r : Fin d → ℝ := fun j => l ^ (s j.succ - s j.castSucc).toNat
  have hr (j : Fin d) : 0 < r j ∧ r j < 1 := by
    have hj := hs (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    have hg : 0 < (s j.succ - s j.castSucc).toNat := by omega
    exact ⟨pow_pos hl _, pow_lt_one₀ hl.le hl1 (by omega)⟩
  have he : observedEntropy (twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)) (d+1) s =
      selectedEntropy t d r := by
    unfold observedEntropy selectedEntropy
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [twoSidedLaw_selected hl hl1 ht ht1 d s hs a]
    change ENNReal.toReal (ENNReal.ofReal (selectedProb t d r a)) *
      Real.log (ENNReal.toReal (ENNReal.ofReal (selectedProb t d r a))) = _
    rw [ENNReal.toReal_ofReal (selectedProb_pos ht ht1 d r hr a).le]
  rw [he, selectedEntropy_eq ht ht1 d r hr]
  unfold initialEntropy
  simp_rw [chart_stationary (ne_of_lt hl1)]
  rfl

def assignmentEquiv {A B : Type*} (e : A ≃ B) : (B → Fin 2) ≃ (A → Fin 2) where
  toFun a j := a (e j)
  invFun w i := w (e.symm i)
  left_inv a := by funext i; simp
  right_inv w := by funext j; simp

/-- Reindexing the actual rank-zero join entropy by a bijective enumeration. -/
theorem rankZeroSampleEntropy_enumerate (μ : Measure (ℤ → Fin 2)) (k : ℤ) (n m : ℕ)
    (S : Finset (Fin (n+1))) (e : Fin m ≃ S) :
    rankZeroSampleEntropy μ k n S =
      observedEntropy μ m (fun j => k+(e j).val.val) := by
  unfold rankZeroSampleEntropy observedEntropy
  congr 1
  apply Fintype.sum_equiv (assignmentEquiv e)
  intro a
  have he : {x : ℤ → Fin 2 | ∀ i : S, x (k+i.val.val) = a i} =
      {x | ∀ j : Fin m, x (k+(e j).val.val) = assignmentEquiv e a j} := by
    ext x
    constructor
    · intro h j; exact h (e j)
    · intro h i
      obtain ⟨j,rfl⟩ := e.surjective i
      exact h j
  rw [he]

/-- Exact source finite-subset entropy under any increasing enumeration.
This eliminates the sparse finite marginal sum from r4. -/
theorem sampleEntropy_selected {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (n d : ℕ)
    (S : Finset (Fin (n+1))) (e : Fin (d+1) ≃ S)
    (he : StrictMono (fun j => (e j).val)) :
    sampleEntropy (chart l t) n S = initialEntropy (chart l t) +
      ∑ j : Fin d, conditionalEntropy
        (l ^ (((e j.succ).val.val : ℤ) - (e j.castSucc).val.val).toNat) t := by
  rw [← rankZeroSampleEntropy_eq (chart l t) (chart_mem_interior hl hl1 ht ht1) 0,
    rankZeroSampleEntropy_enumerate _ 0 n (d+1) S e]
  simpa only [zero_add] using observedEntropy_selected hl hl1 ht ht1 d
    (fun j => ((e j).val.val : ℤ)) (fun i j hij => by
      change ((e i).val.val : ℤ) < ((e j).val.val : ℤ)
      exact Int.ofNat_lt.mpr (he hij))


end
end MathDB333569
