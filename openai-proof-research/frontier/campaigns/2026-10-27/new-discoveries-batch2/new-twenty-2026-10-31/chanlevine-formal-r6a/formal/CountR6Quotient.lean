import CountR6Encoding
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round6
open Polynomial Round3
variable {F : Type*} [Field F]

/-- The actual finite recursion used by the frozen quotientCoeff. -/
def quotientStage (a d : Polynomial F) (r : ℕ) : ℕ → F :=
  Nat.rec (motive := fun _ => ℕ → F) (fun _ => 0)
    (fun r prev j => if j = r then
      a.coeff r - ∑ i : Fin r, d.coeff (r-i.val) * prev i.val
      else prev j) r

theorem quotientStage_value (a d : Polynomial F) (r j : ℕ) (hj : j < r) :
    quotientStage a d r j = quotientCoeff a d j := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases h : j = r
    · subst j; rfl
    · change (if j = r then _ else quotientStage a d r j) = _
      rw [ite_eq_right h]
      exact ih (by omega)

/-- A recurrence theorem for the frozen definition, without a series-division oracle. -/
theorem quotientCoeff_recurrence (a d : Polynomial F) (m : ℕ) :
    quotientCoeff a d m = a.coeff m -
      ∑ i : Fin m, d.coeff (m-i.val) * quotientCoeff a d i.val := by
  change (if m = m then _ else _) = _
  rw [ite_eq_left rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change d.coeff (m-i.val) * quotientStage a d m i.val = _
  rw [quotientStage_value a d m i.val i.isLt]

/-- Any finite convolution satisfying this triangular recurrence is the quotient. -/
theorem quotientCoeff_unique (a d : Polynomial F) (c : ℕ → F)
    (hc : ∀ m, c m = a.coeff m - ∑ i : Fin m, d.coeff (m-i.val) * c i.val) :
    ∀ m, quotientCoeff a d m = c m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [quotientCoeff_recurrence, hc m]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ih i.val i.isLt]

/-- The convolution form with unit constant denominator is enough to identify every coefficient. -/
theorem quotientCoeff_of_convolution (a d : Polynomial F) (hd : d.coeff 0 = 1)
    (c : ℕ → F)
    (hc : ∀ m, a.coeff m = ∑ i : Fin (m+1), d.coeff (m-i.val) * c i.val) :
    ∀ m, quotientCoeff a d m = c m := by
  apply quotientCoeff_unique
  intro m
  have h := hc m
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, hd, one_mul] at h
  linear_combination -h
end ChanLevine.Round6
