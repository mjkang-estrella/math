/-
BiHBridge: the spectral-to-algebraic bridge. If the Laplacian factors as `L = B Bᵀ` with
`Bᵀ 1 = 0`, `M = Bᵀ B` invertible and `ker L` made of constant vectors, then
`BH(G) = n * tr(M⁻²)`.

MathDB 352303 (Z. Lin, arXiv:2110.09931).
-/
import BiHBase
import BiHTrace
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Unitary

namespace BiH

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The bridge.** For a graph whose Laplacian factors as `B * Bᵀ`, with `Bᵀ 1 = 0`, with
`M = Bᵀ * B` invertible with inverse `M'`, and with the kernel of the Laplacian consisting of
constant vectors, the biharmonic index equals `n` times the trace of `M'` squared. -/
theorem bh_eq_card_mul_trace_inv_sq [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Matrix V E ℝ) (M M' : Matrix E E ℝ)
    (hL : G.lapMatrix ℝ = B * Bᵀ)
    (hM : M = Bᵀ * B)
    (hMM' : M * M' = 1) (hM'M : M' * M = 1)
    (hB1 : Bᵀ *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hker : ∀ x : V → ℝ, G.lapMatrix ℝ *ᵥ x = 0 → ∀ i j : V, x i = x j) :
    bh G = (Fintype.card V : ℝ) * (M' * M').trace := by
  classical
  set L : Matrix V V ℝ := G.lapMatrix ℝ with hLdef
  set ones : V → ℝ := fun _ => (1 : ℝ) with hones
  have hLh : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  have hLeq : L = B * Bᵀ := hL
  -- basic facts about `ones`
  have honesdot : ones ⬝ᵥ ones = (Fintype.card V : ℝ) := by
    simp [hones, dotProduct, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardne : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  -- eigenvectors and their norms
  have heig : ∀ i : V, L *ᵥ (hLh.eigenvectorBasis i).ofLp =
      hLh.eigenvalues i • (hLh.eigenvectorBasis i).ofLp :=
    fun i => hLh.mulVec_eigenvectorBasis i
  have horth : ∀ i : V,
      (hLh.eigenvectorBasis i).ofLp ⬝ᵥ (hLh.eigenvectorBasis i).ofLp = 1 := by
    intro i
    have h1 : ‖hLh.eigenvectorBasis i‖ = 1 := hLh.eigenvectorBasis.orthonormal.1 i
    have h2 : inner ℝ (hLh.eigenvectorBasis i) (hLh.eigenvectorBasis i) = (1 : ℝ) := by
      rw [inner_self_eq_norm_sq_to_K, h1]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h2
    exact h2
  -- constant vectors orthogonal to `ones` vanish
  have hconst_zero : ∀ y : V → ℝ, (∀ i j : V, y i = y j) → y ⬝ᵥ ones = 0 → y = 0 := by
    intro y hy hdot
    have hyc : y = y (Classical.arbitrary V) • ones := by
      funext j
      simp [hones, hy j (Classical.arbitrary V)]
    have h2 : y (Classical.arbitrary V) * (Fintype.card V : ℝ) = 0 := by
      have h3 := hdot
      rw [hyc, smul_dotProduct, honesdot] at h3
      exact h3
    have hc : y (Classical.arbitrary V) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hcardne
    rw [hyc, hc, zero_smul]
  -- `Bᵀ` kills constant vectors
  have hBconst : ∀ c : ℝ, Bᵀ *ᵥ (c • ones) = 0 := by
    intro c
    rw [Matrix.mulVec_smul, hB1, smul_zero]
  -- the action of `N = B M'² Bᵀ` on the eigenvectors of `L`
  set N : Matrix V V ℝ := B * (M' * M') * Bᵀ with hNdef
  have hNu_zero : ∀ i : V, hLh.eigenvalues i = 0 →
      N *ᵥ (hLh.eigenvectorBasis i).ofLp = 0 := by
    intro i hi
    have hLu : L *ᵥ (hLh.eigenvectorBasis i).ofLp = 0 := by
      rw [heig i, hi, zero_smul]
    have hkeru : ∀ p q : V,
        (hLh.eigenvectorBasis i).ofLp p = (hLh.eigenvectorBasis i).ofLp q :=
      hker _ (by simpa [← hLdef] using hLu)
    obtain ⟨c, hc⟩ : ∃ c : ℝ, (hLh.eigenvectorBasis i).ofLp = c • ones := by
      refine ⟨(hLh.eigenvectorBasis i).ofLp (Classical.arbitrary V), ?_⟩
      funext j
      simp [hones, hkeru j (Classical.arbitrary V)]
    rw [hNdef, ← Matrix.mulVec_mulVec, hc, hBconst, Matrix.mulVec_zero]
  have hNu_ne : ∀ i : V, hLh.eigenvalues i ≠ 0 →
      N *ᵥ (hLh.eigenvectorBasis i).ofLp =
        (hLh.eigenvalues i)⁻¹ • (hLh.eigenvectorBasis i).ofLp := by
    intro i hi
    have hw : B *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) =
        hLh.eigenvalues i • (hLh.eigenvectorBasis i).ofLp := by
      rw [Matrix.mulVec_mulVec, ← hLeq]
      exact heig i
    have hMw1 : M *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) =
        hLh.eigenvalues i • (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by
      calc M *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)
          = (Bᵀ * B) *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by rw [hM]
        _ = Bᵀ *ᵥ (B *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by
              rw [← Matrix.mulVec_mulVec]
        _ = Bᵀ *ᵥ (hLh.eigenvalues i • (hLh.eigenvectorBasis i).ofLp) := by rw [hw]
        _ = hLh.eigenvalues i • (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by
              rw [Matrix.mulVec_smul]
    have hMw2 : Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp =
        hLh.eigenvalues i •
          (M' *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by
      calc Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp
          = (M' * M) *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by
              rw [hM'M, Matrix.one_mulVec]
        _ = M' *ᵥ (M *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by
              rw [← Matrix.mulVec_mulVec]
        _ = M' *ᵥ (hLh.eigenvalues i • (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by
              rw [hMw1]
        _ = hLh.eigenvalues i •
              (M' *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by
              rw [Matrix.mulVec_smul]
    have hMw : M' *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) =
        (hLh.eigenvalues i)⁻¹ • (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by
      have h := congrArg (fun z => (hLh.eigenvalues i)⁻¹ • z) hMw2
      simp only [smul_smul, inv_mul_cancel₀ hi, one_smul] at h
      exact h.symm
    have hMM'w : (M' * M') *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) =
        ((hLh.eigenvalues i)⁻¹ * (hLh.eigenvalues i)⁻¹) •
          (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by
      rw [← Matrix.mulVec_mulVec, hMw, Matrix.mulVec_smul, hMw, smul_smul]
    calc N *ᵥ (hLh.eigenvectorBasis i).ofLp
        = (B * (M' * M')) *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp) := by
            rw [hNdef, ← Matrix.mulVec_mulVec]
      _ = B *ᵥ ((M' * M') *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by
            rw [← Matrix.mulVec_mulVec]
      _ = B *ᵥ (((hLh.eigenvalues i)⁻¹ * (hLh.eigenvalues i)⁻¹) •
            (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by rw [hMM'w]
      _ = ((hLh.eigenvalues i)⁻¹ * (hLh.eigenvalues i)⁻¹) •
            (B *ᵥ (Bᵀ *ᵥ (hLh.eigenvectorBasis i).ofLp)) := by rw [Matrix.mulVec_smul]
      _ = ((hLh.eigenvalues i)⁻¹ * (hLh.eigenvalues i)⁻¹) •
            (hLh.eigenvalues i • (hLh.eigenvectorBasis i).ofLp) := by rw [hw]
      _ = (hLh.eigenvalues i)⁻¹ • (hLh.eigenvectorBasis i).ofLp := by
            rw [smul_smul, mul_assoc, inv_mul_cancel₀ hi, mul_one]
  -- unitarity of the eigenvector matrix
  have hUtU : (hLh.eigenvectorUnitary : Matrix V V ℝ)ᵀ *
      (hLh.eigenvectorUnitary : Matrix V V ℝ) = 1 := by
    have h := coe_star_mul_self hLh.eigenvectorUnitary
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hUU : (hLh.eigenvectorUnitary : Matrix V V ℝ) *
      (hLh.eigenvectorUnitary : Matrix V V ℝ)ᵀ = 1 := by
    have h : (hLh.eigenvectorUnitary : Matrix V V ℝ) *
        star (hLh.eigenvectorUnitary : Matrix V V ℝ) = 1 :=
      coe_mul_star_self hLh.eigenvectorUnitary
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  -- the trace of `N²`
  have htr : (N * N).trace = ∑ i : V,
      (if hLh.eigenvalues i = 0 then 0 else (hLh.eigenvalues i)⁻¹ ^ 2) := by
    rw [trace_eq_sum_dotProduct_col (N * N) (hLh.eigenvectorUnitary : Matrix V V ℝ) hUtU hUU]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hcol : (fun j : V => (hLh.eigenvectorUnitary : Matrix V V ℝ) j i) =
        (hLh.eigenvectorBasis i).ofLp := by
      funext j
      rw [Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [hcol]
    have h2 : (N * N) *ᵥ (hLh.eigenvectorBasis i).ofLp =
        ((if hLh.eigenvalues i = 0 then 0 else (hLh.eigenvalues i)⁻¹) *
         (if hLh.eigenvalues i = 0 then 0 else (hLh.eigenvalues i)⁻¹)) •
          (hLh.eigenvectorBasis i).ofLp := by
      rw [← Matrix.mulVec_mulVec]
      split_ifs with hi
      · rw [hNu_zero i hi, Matrix.mulVec_zero]
        simp
      · rw [hNu_ne i hi, Matrix.mulVec_smul, hNu_ne i hi, smul_smul]
    rw [h2, dotProduct_smul, horth i]
    split_ifs with hi
    · simp [smul_eq_mul]
    · simp [sq, smul_eq_mul]
  -- the algebraic identity `tr(N²) = tr(M'²)`
  have hmul_sandwich : ∀ X Y : Matrix E E ℝ,
      (B * X * Bᵀ) * (B * Y * Bᵀ) = B * (X * M * Y) * Bᵀ := by
    intro X Y
    conv_lhs => rw [Matrix.mul_assoc]
    conv_lhs => enter [2]; rw [← Matrix.mul_assoc]
    conv_lhs => enter [2, 1]; rw [← Matrix.mul_assoc]
    conv_lhs => enter [2, 1, 1]; rw [← hM]
    conv_lhs => rw [Matrix.mul_assoc]
    conv_lhs => enter [2]; rw [← Matrix.mul_assoc]
    conv_lhs => enter [2, 1]; rw [← Matrix.mul_assoc]
    conv_rhs => rw [Matrix.mul_assoc]
  have hX : (M' * M') * M * (M' * M') = M' * M' * M' := by
    conv_lhs => rw [Matrix.mul_assoc]
    conv_lhs => enter [2]; rw [← Matrix.mul_assoc]
    conv_lhs => enter [2, 1]; rw [hMM']
    conv_lhs => enter [2]; rw [Matrix.one_mul]
  have hNN : N * N = B * (M' * M' * M') * Bᵀ := by
    rw [hNdef, hmul_sandwich (M' * M') (M' * M'), hX]
  have htrM : (N * N).trace = (M' * M').trace := by
    rw [hNN, Matrix.trace_mul_cycle, ← hM]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
  -- assemble
  have hbh : bh G = (Fintype.card V : ℝ) * ∑ i : V,
      (if hLh.eigenvalues i = 0 then 0 else (hLh.eigenvalues i)⁻¹ ^ 2) := by
    unfold bh
    rfl
  rw [hbh, ← htr, htrM]

end BiH
