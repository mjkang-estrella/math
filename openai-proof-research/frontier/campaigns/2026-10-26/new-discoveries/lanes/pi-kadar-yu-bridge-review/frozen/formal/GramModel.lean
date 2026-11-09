import GcdHeadTail

/- One-tail Gram model in the exact alpha*I+G convention of the source.
The head is arbitrary real symmetric, with the attaching coordinate last.
The source interpretation for all partitions is subject to independent review;
this file makes no discovery-credit or representation-theoretic claim. -/
namespace KadarYu

open Matrix Finset Polynomial

theorem headTailMatrix_neg (h : ℕ)
    (A : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (c : ℝ) (s : ℕ) :
    headTailMatrix h (-A) (-c) s = -headTailMatrix h A c s := by
  apply Matrix.ext
  intro i j
  simp only [headTailMatrix, Matrix.neg_apply]
  split_ifs <;> simp

noncomputable def gramModelMatrix (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) :
    Matrix (Fin (h + s + 1)) (Fin (h + s + 1)) (Polynomial ℝ) := fun i j =>
  (if i = j then X else 0) + C (headTailMatrix h G 1 s i j)

theorem gramModelMatrix_eq_charmatrix (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) :
    gramModelMatrix h G s = (headTailMatrix h (-G) (-1) s).charmatrix := by
  rw [headTailMatrix_neg]
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [gramModelMatrix, Matrix.charmatrix_apply_eq]
  · simp [gramModelMatrix, Matrix.charmatrix_apply_ne, hij]

noncomputable def gramModelDeterminant (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) : Polynomial ℝ :=
  (gramModelMatrix h G s).det

theorem gramModelDeterminant_eq (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) :
    gramModelDeterminant h G s = headTailPolynomial h (-G) (-1) s := by
  rw [gramModelDeterminant, gramModelMatrix_eq_charmatrix]
  rfl

noncomputable def gramModelReduced (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) : Polynomial ℝ :=
  gramModelDeterminant h G s /
    GCDMonoid.gcd (gramModelDeterminant h G 0) (gramModelDeterminant h G 1)

theorem gramModelReduced_eq (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ) (s : ℕ) :
    gramModelReduced h G s = headTailReduced h (-G) (-1) s := by
  simp only [gramModelReduced, gramModelDeterminant_eq, headTailReduced, headTailCommonFactor]

theorem gramModelReduced_identification (h : ℕ)
    (G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ)
    (F : Polynomial ℝ) (p : ℕ → Polynomial ℝ) (hF : F.Monic)
    (hcop : IsCoprime (p 0) (p 1))
    (hfac : ∀ s, gramModelDeterminant h G s = F * p s) :
    ∀ s, p s = gramModelReduced h G s := by
  have hdet : ∀ s, F * p s = headTailCommonFactor h (-G) (-1) *
      headTailReduced h (-G) (-1) s := by
    intro s
    rw [← hfac s, gramModelDeterminant_eq, headTailReduced_factor]
  obtain ⟨_, heq⟩ := reduced_series_identification hF
    (headTailCommonFactor_monic h (-G) (-1)) hcop
    (headTailReduced_coprime h (-G) (-1) (by norm_num) 0) hdet
  intro s
  exact (heq s).trans (gramModelReduced_eq h G s).symm

theorem gramModelReduced_splits (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) (s : ℕ) :
    (gramModelReduced h G s).Splits := by
  rw [gramModelReduced_eq]
  apply (headTailMatrix_hermitian h hG.neg (-1) s).splits_charpoly.of_dvd
    (Matrix.charpoly_monic _).ne_zero
  exact ⟨headTailCommonFactor h (-G) (-1),
    (headTailReduced_factor h (-G) (-1) s).trans (mul_comm _ _)⟩

theorem gramModelBoundary_splits (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) :
    (X * gramModelReduced h G 0 - gramModelReduced h G 1).Splits := by
  simp_rw [gramModelReduced_eq]
  have hm := headTail_boundary_factor h (-G) (-1) (by norm_num)
    (headTailCommonFactor h (-G) (-1)) (headTailReduced h (-G) (-1) 0)
    (headTailReduced h (-G) (-1) 1) (headTailReduced_factor h (-G) (-1) 0)
    (headTailReduced_factor h (-G) (-1) 1)
  apply (hG.neg.submatrix Fin.castSucc).splits_charpoly.of_dvd
    (Matrix.charpoly_monic _).ne_zero
  exact ⟨headTailCommonFactor h (-G) (-1), hm.trans (mul_comm _ _)⟩

theorem gramModelReduced_root_distribution (h : ℕ)
    {G : Matrix (Fin (h + 1)) (Fin (h + 1)) ℝ} (hG : G.IsHermitian) :
    Squarefree (X * gramModelReduced h G 0 - gramModelReduced h G 1) ∧
    (∀ s, Squarefree (gramModelReduced h G s)) ∧
    (∃ N C : ℕ, C ≤ 2 * (h + 1) ∧ ∀ s, N ≤ s →
      exteriorRootCount (gramModelReduced h G s) = C) ∧
    Set.Icc (-2 : ℝ) 2 ⊆ closure
      {y : ℝ | y ∈ Set.Icc (-2 : ℝ) 2 ∧ ∃ s : ℕ, (gramModelReduced h G s).eval y = 0} := by
  simp_rw [gramModelReduced_eq]
  exact headTailReduced_root_distribution h hG.neg (-1) (by norm_num)

end KadarYu
