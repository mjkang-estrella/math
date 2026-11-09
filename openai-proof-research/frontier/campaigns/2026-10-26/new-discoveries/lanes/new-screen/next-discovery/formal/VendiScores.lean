import VendiMatrix

open Finset Real Matrix
namespace VendiScores

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def sizeReal : ℝ := Fintype.card I
noncomputable def rowSum (Z : Matrix I I ℝ) (i : I) : ℝ := ∑ j,Z i j

omit [DecidableEq I] in
lemma sizeReal_pos : (0:ℝ)<sizeReal (I:=I) := by
  unfold sizeReal
  exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)

omit [DecidableEq I] [Nonempty I] in
lemma rowSum_ge_one (Z : Matrix I I ℝ) (hdiag : ∀ i,Z i i=1)
    (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) (i : I) : 1≤rowSum Z i := by
  have h := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (hentry i j).1) (Finset.mem_univ i)
  simpa [hdiag,rowSum] using h

omit [DecidableEq I] [Nonempty I] in
lemma rowSum_pos (Z : Matrix I I ℝ) (hdiag : ∀ i,Z i i=1)
    (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) (i : I) : 0<rowSum Z i := by
  have h := rowSum_ge_one Z hdiag hentry i
  linarith

noncomputable def vendiInner {Z : Matrix I I ℝ} (hZ : Z.PosSemidef) (q : ℝ) : ℝ :=
  ∑ j∈VendiMatrix.positiveSpectrum hZ,(hZ.1.eigenvalues j/sizeReal (I:=I))^q

noncomputable def lcrInner (Z : Matrix I I ℝ) (q : ℝ) : ℝ :=
  (1/sizeReal (I:=I))*∑ i,(rowSum Z i/sizeReal (I:=I))^(q-1)

noncomputable def vendiScore {Z : Matrix I I ℝ} (hZ : Z.PosSemidef) (q : ℝ) : ℝ :=
  (vendiInner hZ q)^(1/(1-q))

noncomputable def lcrScore (Z : Matrix I I ℝ) (q : ℝ) : ℝ :=
  (lcrInner Z q)^(1/(1-q))

lemma vendiInner_factor {Z : Matrix I I ℝ} (hZ : Z.PosSemidef) (q : ℝ) :
    vendiInner hZ q=(sizeReal (I:=I))^(-q)*
      ∑ j∈VendiMatrix.positiveSpectrum hZ,(hZ.1.eigenvalues j)^q := by
  unfold vendiInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.div_rpow (hZ.eigenvalues_nonneg j) sizeReal_pos.le,
    Real.rpow_neg sizeReal_pos.le]
  ring

omit [DecidableEq I] in
lemma lcrInner_factor (Z : Matrix I I ℝ) (hdiag : ∀ i,Z i i=1)
    (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) (q : ℝ) :
    lcrInner Z q=(sizeReal (I:=I))^(-q)*∑ i,(rowSum Z i)^(q-1) := by
  unfold lcrInner
  simp_rw [Real.div_rpow (rowSum_pos Z hdiag hentry _).le sizeReal_pos.le]
  rw [← Finset.sum_div, Real.rpow_sub sizeReal_pos, Real.rpow_one,
    Real.rpow_neg sizeReal_pos.le]
  have hn := sizeReal_pos (I:=I)
  have hp := Real.rpow_pos_of_pos hn q
  field_simp

omit [DecidableEq I] in
lemma lcrInner_nonneg (Z : Matrix I I ℝ) (hdiag : ∀ i,Z i i=1)
    (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) (q : ℝ) : 0≤lcrInner Z q := by
  rw [lcrInner_factor Z hdiag hentry]
  apply mul_nonneg (Real.rpow_pos_of_pos sizeReal_pos _).le
  exact Finset.sum_nonneg (fun i _ => (Real.rpow_pos_of_pos (rowSum_pos Z hdiag hentry i) _).le)

/-- The exact uniform VS/LCR definitions compare at every finite real order below one. -/
theorem source_scores_below_one (Z : Matrix I I ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1)
    (q : ℝ) (hq : q<1) : lcrScore Z q≤vendiScore hZ q := by
  unfold lcrScore vendiScore
  apply Real.rpow_le_rpow (lcrInner_nonneg Z hdiag hentry q) _
    (le_of_lt (one_div_pos.mpr (sub_pos.mpr hq)))
  rw [lcrInner_factor Z hdiag hentry, vendiInner_factor]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos sizeReal_pos _).le
  exact VendiMatrix.source_spectral_row_bound Z hZ hdiag hentry q hq

/-- The remaining singular negative-order case of the source conjecture. -/
theorem source_conjecture_negative (Z : Matrix I I ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1)
    (q : ℝ) (hq : q<0) : lcrScore Z q≤vendiScore hZ q := by
  exact source_scores_below_one Z hZ hdiag hentry q (by linarith)

lemma positiveSpectrum_nonempty {Z : Matrix I I ℝ} (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) : (VendiMatrix.positiveSpectrum hZ).Nonempty := by
  classical
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  let i : I := Classical.choice inferInstance
  have h := VendiMatrix.support_diag_frame hZ i
  simp [he,hdiag] at h

noncomputable def positiveValues {Z : Matrix I I ℝ} (hZ : Z.PosSemidef) : Finset ℝ :=
  (VendiMatrix.positiveSpectrum hZ).image hZ.1.eigenvalues

lemma positiveValues_nonempty {Z : Matrix I I ℝ} (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) : (positiveValues hZ).Nonempty :=
  (positiveSpectrum_nonempty hZ hdiag).image _

noncomputable def minPositiveEigenvalue {Z : Matrix I I ℝ} (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) : ℝ :=
  (positiveValues hZ).min' (positiveValues_nonempty hZ hdiag)

lemma minPositiveEigenvalue_pos {Z : Matrix I I ℝ} (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) : 0 < minPositiveEigenvalue hZ hdiag := by
  have hm := Finset.min'_mem (positiveValues hZ) (positiveValues_nonempty hZ hdiag)
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
  have hp := (Finset.mem_filter.mp hj).2
  change 0 < (positiveValues hZ).min' _
  rw [← he]
  exact hp

lemma minPositiveEigenvalue_le {Z : Matrix I I ℝ} (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) {j : I} (hj : j∈VendiMatrix.positiveSpectrum hZ) :
    minPositiveEigenvalue hZ hdiag≤hZ.1.eigenvalues j :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj)

noncomputable def rowValues (Z : Matrix I I ℝ) : Finset ℝ :=
  Finset.univ.image (rowSum Z)

omit [DecidableEq I] in
lemma rowValues_nonempty (Z : Matrix I I ℝ) : (rowValues Z).Nonempty :=
  Finset.univ_nonempty.image _

noncomputable def minRowSum (Z : Matrix I I ℝ) : ℝ :=
  (rowValues Z).min' (rowValues_nonempty Z)

lemma minPositiveEigenvalue_le_minRow (Z : Matrix I I ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) :
    minPositiveEigenvalue hZ hdiag ≤ minRowSum Z := by
  have hm := Finset.min'_mem (rowValues Z) (rowValues_nonempty Z)
  obtain ⟨i,_,he⟩ := Finset.mem_image.mp hm
  change rowSum Z i=minRowSum Z at he
  rw [← he]
  exact VendiMatrix.source_min_le_row Z hZ hdiag hentry _
    (fun j hj => minPositiveEigenvalue_le hZ hdiag hj) i

noncomputable def negativeInfinityVendi {Z : Matrix I I ℝ} (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) : ℝ := sizeReal (I:=I)/minPositiveEigenvalue hZ hdiag

noncomputable def negativeInfinityLcr (Z : Matrix I I ℝ) : ℝ :=
  sizeReal (I:=I)/minRowSum Z

/-- The same source comparison at order minus infinity, using the positive spectral support. -/
theorem source_conjecture_negativeInfinity (Z : Matrix I I ℝ) (hZ : Z.PosSemidef)
    (hdiag : ∀ i,Z i i=1) (hentry : ∀ i j,0≤Z i j ∧ Z i j≤1) :
    negativeInfinityLcr Z≤negativeInfinityVendi hZ hdiag := by
  exact div_le_div_of_nonneg_left sizeReal_pos.le (minPositiveEigenvalue_pos hZ hdiag)
    (minPositiveEigenvalue_le_minRow Z hZ hdiag hentry)

end VendiScores
