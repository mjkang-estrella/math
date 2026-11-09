import SourceRecurrence
open PowerSeries
open scoped PowerSeries
namespace TrigSource

/-- Coefficients of the normalized formal square root of 1+X+...+X^(D-1). -/
noncomputable def sourceCoeff (D k : ℕ) : ℝ := coeff k (sourceRoot D)

lemma sourceCoeff_zero (D : ℕ) (hD : 0<D) : sourceCoeff D 0=1 := by
  rw [sourceCoeff, coeff_zero_eq_constantCoeff_apply, sourceRoot_constant D hD]

lemma sourceCoeff_recurrence (D : ℕ) (hD : 0<D) (k : ℕ) (hk : 1≤k) :
    CoeffRec D (sourceCoeff D) k :=
  root_coeff_recurrence D hD (sourceRoot D) (sourceRoot_identity D hD) k hk

/-- The defining square and its normalized constant select exactly the source root. -/
lemma normalized_root_unique (D : ℕ) (hD : 0<D) (B : PowerSeries ℝ)
    (hB0 : coeff 0 B=1) (hBsq : B^2=geometric D) : B=sourceRoot D := by
  have hs : B^2=(sourceRoot D)^2 := hBsq.trans (sourceRoot_square D hD).symm
  have hf : (B-sourceRoot D)*(B+sourceRoot D)=0 := by linear_combination hs
  rcases mul_eq_zero.mp hf with h | h
  · exact sub_eq_zero.mp h
  · have hc := congrArg (fun F : PowerSeries ℝ => coeff 0 F) h
    simp only [map_add, map_zero, hB0, coeff_zero_eq_constantCoeff_apply, sourceRoot_constant D hD] at hc
    norm_num at hc

/-- Any finite exact recurrence certificate agrees with every needed source coefficient. -/
theorem sourceCoeff_matches (D N : ℕ) (hD : 0<D) (a : ℕ → ℝ)
    (ha0 : a 0=1) (ha : ∀ k, 1≤k → k≤N → CoeffRec D a k) :
    ∀ k, k≤N → sourceCoeff D k=a k := by
  apply recurrence_unique_upto hD
  · rw [sourceCoeff_zero D hD, ha0]
  · intro k hk _
    exact sourceCoeff_recurrence D hD k hk
  · exact ha

/-- The bridge also applies directly to the coefficients of any normalized source root. -/
theorem rootCoeff_matches (D N : ℕ) (hD : 0<D) (B : PowerSeries ℝ)
    (hB0 : coeff 0 B=1) (hBsq : B^2=geometric D) (a : ℕ → ℝ)
    (ha0 : a 0=1) (ha : ∀ k, 1≤k → k≤N → CoeffRec D a k) :
    ∀ k, k≤N → coeff k B=a k := by
  rw [normalized_root_unique D hD B hB0 hBsq]
  exact sourceCoeff_matches D N hD a ha0 ha

end TrigSource
