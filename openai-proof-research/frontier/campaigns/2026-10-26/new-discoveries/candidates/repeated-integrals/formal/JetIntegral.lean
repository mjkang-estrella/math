import StieltjesData

open Set
open scoped ContDiff

namespace RepeatedIntegrals

theorem iteratedWithin_iterated (i j : ℕ) (f : ℝ → ℝ) (s : Set ℝ) :
    iteratedDerivWithin i (iteratedDerivWithin j f s) s =
      iteratedDerivWithin (i + j) f s := by
  let D : (ℝ → ℝ) → (ℝ → ℝ) := fun g => derivWithin g s
  have h (k : ℕ) (g : ℝ → ℝ) : iteratedDerivWithin k g s = D^[k] g := by
    funext x
    exact iteratedDerivWithin_eq_iterate
  rw [h i (iteratedDerivWithin j f s), h j f, h (i + j) f,
    Function.iterate_add_apply]

theorem contDiffOn_iteratedWithin {f : ℝ → ℝ} {n j k : ℕ}
    (hf : ContDiffOn ℝ n f (Icc (0 : ℝ) 1)) (hjk : j + k ≤ n) :
    ContDiffOn ℝ k (iteratedDerivWithin j f (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) := by
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv uniqueDiffOn_Icc_zero_one]
  constructor
  · intro i hi
    rw [iteratedWithin_iterated]
    apply hf.continuousOn_iteratedDerivWithin _ uniqueDiffOn_Icc_zero_one
    exact_mod_cast (show i + j ≤ n by omega)
  · intro i hi
    rw [iteratedWithin_iterated]
    apply hf.differentiableOn_iteratedDerivWithin _ uniqueDiffOn_Icc_zero_one
    exact_mod_cast (show i + j < n by omega)

theorem taylor_zero_of_initial_jets (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (x : ℝ)
    (h0 : ∀ j ≤ n, iteratedDerivWithin j f s 0 = 0) :
    taylorWithinEval f n s 0 x = 0 := by
  induction n with
  | zero =>
    simpa [taylorWithinEval, taylorWithin, taylorCoeffWithin] using h0 0 le_rfl
  | succ n ih =>
    rw [taylorWithinEval_succ, ih (fun j hj => h0 j (by omega)), h0 (n + 1) le_rfl]
    simp

theorem source_jet_integral {f : ℝ → ℝ} (j k : ℕ)
    (hf : ContDiffOn ℝ (j + k + 1 : ℕ) f (Icc (0 : ℝ) 1))
    (h0 : ∀ i ≤ j + k, iteratedDerivWithin i f (Icc (0 : ℝ) 1) 0 = 0) :
    iteratedDerivWithin j f (Icc (0 : ℝ) 1) 1 =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / k.factorial) *
        iteratedDerivWithin (j + k + 1) f (Icc (0 : ℝ) 1) t := by
  have hg : ContDiffOn ℝ (k + 1 : ℕ) (iteratedDerivWithin j f (Icc (0 : ℝ) 1))
      (Icc (0 : ℝ) 1) := contDiffOn_iteratedWithin hf (by omega)
  have ht := taylor_integral_remainder (f := iteratedDerivWithin j f (Icc (0 : ℝ) 1))
    (n := k) (x₀ := (0 : ℝ)) (x := (1 : ℝ))
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hg)
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hz : taylorWithinEval (iteratedDerivWithin j f (Icc (0 : ℝ) 1)) k
      (Icc (0 : ℝ) 1) 0 1 = 0 := by
    apply taylor_zero_of_initial_jets
    intro i hi
    rw [iteratedWithin_iterated]
    exact h0 (i + j) (by omega)
  rw [hz, sub_zero] at ht
  simpa only [iteratedWithin_iterated, smul_eq_mul,
    show k + 1 + j = j + k + 1 by omega] using ht

end RepeatedIntegrals
