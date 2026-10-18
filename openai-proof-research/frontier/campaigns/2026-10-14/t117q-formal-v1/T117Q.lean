import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! Scoped T117Q support. Original code: Myeongjin Kang, MIT.
Matrix inequalities below use the Loewner order, not entrywise order.
No Gaussian integration, fractional powers, or metric construction is encoded. -/
open scoped MatrixOrder ComplexOrder
open Matrix Unitary
namespace T117Q
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def realTrace (A : Matrix n n ℂ) : ℝ := A.trace.re

noncomputable def model (U : unitary (Matrix n n ℂ)) (lam : n → ℝ) : Matrix n n ℂ :=
  conjStarAlgAut ℂ _ U (diagonal fun i => (lam i : ℂ))

noncomputable def cutoff (U : unitary (Matrix n n ℂ)) (lam : n → ℝ) (h : ℝ) :
    Matrix n n ℂ := model U (fun i => if lam i ≤ h then 1 else 0)

theorem model_mono (U : unitary (Matrix n n ℂ)) {a b : n → ℝ}
    (hab : ∀ i, a i ≤ b i) : model U a ≤ model U b := by
  apply OrderHomClass.mono (conjStarAlgAut ℂ _ U)
  rw [Matrix.le_iff, diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  exact sub_nonneg.mpr (RCLike.ofReal_le_ofReal.mpr (hab i))

theorem model_sub (U : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    model U (a - b) = model U a - model U b := by
  unfold model
  rw [← map_sub, diagonal_sub]
  simp only [Pi.sub_apply, Complex.ofReal_sub]

theorem model_smul (U : unitary (Matrix n n ℂ)) (a : n → ℝ) (r : ℝ) :
    model U (r • a) = r • model U a := by
  have hd : (diagonal fun i => ((r • a) i : ℂ)) = r • (diagonal fun i => (a i : ℂ)) := by
    rw [← diagonal_smul]
    congr 1
    funext i
    simp
  unfold model
  rw [hd]
  simp only [conjStarAlgAut_apply, Matrix.mul_smul, Matrix.smul_mul]

theorem model_one (U : unitary (Matrix n n ℂ)) : model U (fun _ => 1) = 1 := by
  simp [model]

theorem model_zero (U : unitary (Matrix n n ℂ)) : model U (fun _ => 0) = 0 := by
  simp [model]

theorem model_mul (U : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    model U a * model U b = model U (a * b) := by
  unfold model
  rw [← map_mul, diagonal_mul_diagonal]
  simp only [Pi.mul_apply, Complex.ofReal_mul]

theorem cutoff_nonneg (U : unitary (Matrix n n ℂ)) (lam : n → ℝ) (h : ℝ) :
    0 ≤ cutoff U lam h := by
  rw [← model_zero U]
  apply model_mono
  intro i
  split_ifs <;> norm_num

theorem cutoff_le_one (U : unitary (Matrix n n ℂ)) (lam : n → ℝ) (h : ℝ) :
    cutoff U lam h ≤ 1 := by
  rw [← model_one U]
  apply model_mono
  intro i
  split_ifs <;> norm_num

theorem cutoff_idempotent (U : unitary (Matrix n n ℂ)) (lam : n → ℝ) (h : ℝ) :
    cutoff U lam h * cutoff U lam h = cutoff U lam h := by
  rw [cutoff, model_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply]
  split_ifs <;> norm_num

theorem cutoff_defect (U : unitary (Matrix n n ℂ)) {lam : n → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (h : ℝ) :
    h • (1 - cutoff U lam h) ≤ model U lam := by
  rw [← model_one U, cutoff, ← model_sub, ← model_smul]
  apply model_mono
  intro i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  split_ifs with hi
  · simpa using hlam i
  · simp only [sub_zero, mul_one]
    exact le_of_lt (lt_of_not_ge hi)

theorem cutoff_compression (U : unitary (Matrix n n ℂ)) (lam : n → ℝ) (h : ℝ) :
    cutoff U lam h * model U lam * cutoff U lam h ≤ h • cutoff U lam h := by
  simp only [cutoff, model_mul, ← model_smul]
  apply model_mono
  intro i
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hi
  · simpa using hi
  · simp

theorem trace_product_nonneg {A B : Matrix n n ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ realTrace (A * B) := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  have h := (hB.posSemidef.mul_mul_conjTranspose_same C).trace_nonneg
  have hr := (RCLike.nonneg_iff.mp h).1
  unfold realTrace
  rw [← Matrix.trace_mul_cycle]
  exact hr


noncomputable def spectralCut (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ) : Matrix n n ℂ :=
  cutoff hQ.posSemidef.isHermitian.eigenvectorUnitary
    hQ.posSemidef.isHermitian.eigenvalues h

theorem spectral_model (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) :
    Q = model hQ.posSemidef.isHermitian.eigenvectorUnitary
      hQ.posSemidef.isHermitian.eigenvalues := by
  exact hQ.posSemidef.isHermitian.spectral_theorem

theorem spectralCut_nonneg (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ) :
    0 ≤ spectralCut Q hQ h := cutoff_nonneg _ _ _

theorem spectralCut_le_one (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ) :
    spectralCut Q hQ h ≤ 1 := cutoff_le_one _ _ _

theorem spectralCut_idempotent (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ) :
    spectralCut Q hQ h * spectralCut Q hQ h = spectralCut Q hQ h :=
  cutoff_idempotent _ _ _

theorem spectralCut_defect (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ) :
    h • (1 - spectralCut Q hQ h) ≤ Q := by
  conv_rhs => rw [spectral_model Q hQ]
  exact cutoff_defect _ hQ.posSemidef.eigenvalues_nonneg h

theorem spectralCut_compression (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ) :
    spectralCut Q hQ h * Q * spectralCut Q hQ h ≤ h • spectralCut Q hQ h := by
  conv_lhs => arg 1; arg 2; rw [spectral_model Q hQ]
  exact cutoff_compression _ _ _

theorem trace_product_mono {Y A B : Matrix n n ℂ}
    (hY : 0 ≤ Y) (hAB : A ≤ B) : realTrace (Y * A) ≤ realTrace (Y * B) := by
  have ht := trace_product_nonneg hY (sub_nonneg.mpr hAB)
  simpa [realTrace, Matrix.mul_sub, Matrix.trace_sub] using ht


omit [DecidableEq n] in
theorem congruence_mono (C : Matrix n n ℂ) {A B : Matrix n n ℂ}
    (hAB : A ≤ B) : C * A * Cᴴ ≤ C * B * Cᴴ := by
  rw [Matrix.le_iff]
  have hp := (sub_nonneg.mpr hAB).posSemidef.mul_mul_conjTranspose_same C
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using hp

theorem spectralCut_domination (Q : Matrix n n ℂ) (hQ : 0 ≤ Q) (h : ℝ)
    {Z : Matrix n n ℂ} (hZ : Zᴴ * Z ≤ Q) :
    spectralCut Q hQ h * (Zᴴ * Z) * spectralCut Q hQ h ≤ h • spectralCut Q hQ h := by
  have hc := congruence_mono (spectralCut Q hQ h) hZ
  have hs := (spectralCut_nonneg Q hQ h).posSemidef.isHermitian
  rw [hs.eq] at hc
  exact hc.trans (spectralCut_compression Q hQ h)

theorem selector_coverage {ι : Type*} (s : Finset ι)
    (Q P : ι → Matrix n n ℂ) {h α : ℝ} (hh : 0 < h)
    (hdef : ∀ i ∈ s, h • (1 - P i) ≤ Q i)
    (hbudget : (∑ i ∈ s, Q i) ≤ h • ((∑ _i ∈ s, (1 : Matrix n n ℂ)) - α • 1)) :
    α • (1 : Matrix n n ℂ) ≤ ∑ i ∈ s, P i := by
  have hd := Finset.sum_le_sum hdef
  have ht : h • ((∑ _i ∈ s, (1 : Matrix n n ℂ)) - ∑ i ∈ s, P i) ≤
      h • ((∑ _i ∈ s, (1 : Matrix n n ℂ)) - α • 1) := by
    simpa only [Finset.smul_sum, Finset.sum_sub_distrib, smul_sub] using hd.trans hbudget
  have hc := smul_le_smul_of_nonneg_left ht (le_of_lt (inv_pos.mpr hh))
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hh), one_smul] at hc
  exact (sub_le_sub_iff_left _).mp hc

theorem spectral_coverage {ι : Type*} (s : Finset ι)
    (Q : ι → Matrix n n ℂ) (hQ : ∀ i, 0 ≤ Q i) {h α : ℝ} (hh : 0 < h)
    (hbudget : (∑ i ∈ s, Q i) ≤ h • ((∑ _i ∈ s, (1 : Matrix n n ℂ)) - α • 1)) :
    α • (1 : Matrix n n ℂ) ≤ ∑ i ∈ s, spectralCut (Q i) (hQ i) h := by
  exact selector_coverage s Q (fun i => spectralCut (Q i) (hQ i) h) hh
    (fun i _ => spectralCut_defect (Q i) (hQ i) h) hbudget

theorem positive_trace_coverage {ι : Type*} (s : Finset ι)
    (P : ι → Matrix n n ℂ) {Y : Matrix n n ℂ} (hY : 0 ≤ Y) {α : ℝ}
    (hcoverage : α • (1 : Matrix n n ℂ) ≤ ∑ i ∈ s, P i) :
    α * realTrace Y ≤ ∑ i ∈ s, realTrace (Y * P i) := by
  have ht := trace_product_mono hY hcoverage
  simpa [realTrace, Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_sum] using ht


theorem spectral_half_coverage {ι : Type*} (s : Finset ι)
    (Q : ι → Matrix n n ℂ) (hQ : ∀ i, 0 ≤ Q i) {h : ℝ} (hh : 0 < h)
    (hbudget : (∑ i ∈ s, Q i) ≤ (h * (s.card : ℝ) / 2) • (1 : Matrix n n ℂ)) :
    ((s.card : ℝ) / 2) • (1 : Matrix n n ℂ) ≤
      ∑ i ∈ s, spectralCut (Q i) (hQ i) h := by
  apply spectral_coverage s Q hQ hh
  convert hbudget using 1
  simp only [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  module

theorem spectral_trace_bound {ι : Type*} (s : Finset ι)
    (Q : ι → Matrix n n ℂ) (hQ : ∀ i, 0 ≤ Q i) {h : ℝ} (hh : 0 < h)
    (hbudget : (∑ i ∈ s, Q i) ≤ (h * (s.card : ℝ) / 2) • (1 : Matrix n n ℂ))
    {Y : Matrix n n ℂ} (hY : 0 ≤ Y) :
    ((s.card : ℝ) / 2) * realTrace Y ≤
      ∑ i ∈ s, realTrace (Y * spectralCut (Q i) (hQ i) h) :=
  positive_trace_coverage s _ hY (spectral_half_coverage s Q hQ hh hbudget)

theorem trace_budget_consequence {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → Matrix n n ℂ) (hQ : ∀ i, 0 ≤ Q i) {h : ℝ} (hh : 0 < h)
    (hbudget : (∑ i ∈ s, Q i) ≤ (h * (s.card : ℝ) / 2) • (1 : Matrix n n ℂ))
    {Y : Matrix n n ℂ} (hY : 0 ≤ Y) {b : ℝ}
    (hb : ∀ i ∈ s, realTrace (Y * spectralCut (Q i) (hQ i) h) ≤ b) :
    realTrace Y ≤ 2 * b := by
  have hl := spectral_trace_bound s Q hQ hh hbudget hY
  have hu := Finset.sum_le_sum hb
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hu
  nlinarith

end T117Q
