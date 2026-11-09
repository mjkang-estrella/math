import RootNewton
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

noncomputable section
open Finset Polynomial
namespace OddRootMeans

/-- The polynomial binomial(T,i)/T, only used when i>0. -/
def binomQuot (i : ℕ) : ℂ[X] :=
  C ((i.factorial : ℂ)⁻¹) * (descPochhammer ℂ (i - 1)).comp (X - 1)

def binomPoly (i : ℕ) : ℂ[X] := if i = 0 then 1 else X * binomQuot i

lemma binomPoly_succ (i : ℕ) : binomPoly (i + 1) =
    C (((i+1).factorial : ℂ)⁻¹) * descPochhammer ℂ (i+1) := by
  simp only [binomPoly, Nat.succ_ne_zero, ↓reduceIte, binomQuot,
    Nat.add_sub_cancel, descPochhammer_succ_left]
  ring

lemma binomPoly_eval_nat (m i : ℕ) : (binomPoly i).eval (m : ℂ) = (m.choose i : ℂ) := by
  cases i with
  | zero => simp [binomPoly]
  | succ i =>
    rw [binomPoly_succ, eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div ℂ]
    rw [div_eq_mul_inv, mul_comm]

lemma binomQuot_degree (i : ℕ) : (binomQuot i).natDegree ≤ i - 1 := by
  unfold binomQuot
  exact (natDegree_C_mul_le _ _).trans (by
    rw [natDegree_comp, descPochhammer_natDegree]
    have hx : (X - (1 : ℂ[X])).natDegree = 1 := by
      simpa only [map_one] using (natDegree_X_sub_C (1 : ℂ))
    simp [hx])

lemma binomPoly_degree (i : ℕ) : (binomPoly i).natDegree ≤ i := by
  by_cases hi : i=0
  · simp [hi, binomPoly]
  · simp only [binomPoly, hi, ↓reduceIte]
    exact natDegree_mul_le.trans (by
      have := binomQuot_degree i
      simp only [natDegree_X]
      omega)

lemma binomPoly_eval_zero (i : ℕ) (hi : 0 < i) : (binomPoly i).eval 0 = 0 := by
  simp [binomPoly, Nat.ne_of_gt hi]

lemma descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℂ n).eval (-1) = (-1 : ℂ)^n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring

lemma binomQuot_zero (n : ℕ) :
    ((n+1 : ℕ) : ℂ) * (binomQuot (n+1)).eval 0 = (-1 : ℂ)^n := by
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [binomQuot, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one,
    zero_sub, Nat.add_sub_cancel, descPochhammer_eval_neg_one, Nat.factorial_succ,
    Nat.cast_mul]
  field_simp


/-- Polynomial continuation of normalized root power sums. -/
def normMoment (a : ℕ → ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n+1 => -(∑ k : Fin n, binomPoly (k+1) * C (a (k+1)) * normMoment a (n-k)) -
      C ((n+1) * a (n+1)) * binomQuot (n+1)
termination_by i => i

lemma normMoment_degree (a : ℕ → ℂ) (i : ℕ) :
    (normMoment a i).natDegree ≤ i-1 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [normMoment]
    | succ n =>
      rw [normMoment]
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · rw [natDegree_neg]
        apply natDegree_sum_le_of_forall_le
        intro k _
        apply natDegree_mul_le.trans
        have hdeg := ih (n-k) (by omega)
        have hbin := binomPoly_degree (k+1)
        have hmul := (natDegree_mul_le (p := binomPoly (k+1)) (q := C (a (k+1))))
        simp only [natDegree_C, add_zero] at hmul
        have hk := k.isLt
        omega
      · exact (natDegree_C_mul_le _ _).trans (binomQuot_degree (n+1))

lemma normMoment_eval_zero (a : ℕ → ℂ) (n : ℕ) :
    (normMoment a (n+1)).eval 0 = (-1 : ℂ)^(n+1) * a (n+1) := by
  rw [normMoment]
  simp only [eval_sub, eval_neg, eval_finsetSum, eval_mul, eval_C]
  have hz : (∑ k : Fin n, (binomPoly (k+1)).eval 0 * a (k+1) *
      (normMoment a (n-k)).eval 0) = 0 := by
    apply sum_eq_zero
    intro k _
    rw [binomPoly_eval_zero _ (by omega)]
    ring
  rw [hz, neg_zero, zero_sub, pow_succ]
  have hb := binomQuot_zero n
  push_cast at hb
  linear_combination -a (n+1) * hb


lemma binomQuot_eval_mul (m n : ℕ) :
    (m : ℂ) * (binomQuot (n+1)).eval (m : ℂ) = (m.choose (n+1) : ℂ) := by
  have h := binomPoly_eval_nat m (n+1)
  simpa only [binomPoly, Nat.succ_ne_zero, ↓reduceIte, eval_mul, eval_X] using h

lemma normMoment_eval_roots (p : ℂ[X]) (hp : p.Monic) (m : ℕ)
    (hm : p.natDegree = m) (a : ℕ → ℂ)
    (hc : ∀ i ≤ m, p.coeff (m-i) = (m.choose i : ℂ) * a i) (i : ℕ) :
    (m : ℂ) * (normMoment a i).eval (m : ℂ) = powerSum p.roots i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero =>
      simp [normMoment, powerSum, ← hm, (IsAlgClosed.splits p).natDegree_eq_card_roots]
    | succ n =>
      rw [normMoment, monic_newton_coeff p hp m hm a hc n]
      simp only [eval_sub, eval_neg, eval_finsetSum, eval_mul, eval_C,
        binomPoly_eval_nat, mul_sub, mul_neg, mul_sum]
      have hs : (∑ k : Fin n, (m:ℂ) * ((m.choose ((k:ℕ)+1) : ℂ) * a ((k:ℕ)+1) *
          (normMoment a (n-k)).eval (m : ℂ))) =
          ∑ k : Fin n, (m.choose ((k:ℕ)+1) : ℂ) * a ((k:ℕ)+1) *
            powerSum p.roots (n-k) := by
        apply sum_congr rfl
        intro k _
        rw [mul_left_comm (m:ℂ), mul_assoc, ih (n-k) (by omega)]
        ring
      rw [hs]
      have hb := binomQuot_eval_mul m n
      linear_combination -(n+1 : ℂ) * a (n+1) * hb

end OddRootMeans
