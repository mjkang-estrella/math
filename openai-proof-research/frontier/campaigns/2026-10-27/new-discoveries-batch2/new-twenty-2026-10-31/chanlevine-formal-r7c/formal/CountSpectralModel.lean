import CountSpectralAlgebra
import Mathlib.Algebra.Polynomial.Basic
open scoped Matrix
noncomputable section
namespace ChanLevine.Round3
open Polynomial
variable {F : Type*} [Field F]

/-- Polynomial transfer factors, in their cyclic order. -/
def transferFactor (z : F) (k : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial F) :=
  dominoMatrix (Polynomial.C z) (1-X*Polynomial.C (z^k))

def transferProduct (z : F) (n : ℕ) := orderedProduct (transferFactor z) n

def denominator (z : F) (n : ℕ) : Polynomial F :=
  orderedProduct (fun k => 1-X*Polynomial.C (z^k)) n

theorem denominator_constant (z : F) (r : ℕ) :
    (denominator z r).coeff 0 = 1 := by
  induction r with
  | zero => simp [denominator, orderedProduct]
  | succ r ih =>
    change (denominator z r * (1-X*Polynomial.C (z^r))).coeff 0 = 1
    simp [Polynomial.coeff_mul, ih]

theorem transferFactor_period (z : F) (e : ℕ) (h : z^e = 1) (k : ℕ) :
    transferFactor z (e+k) = transferFactor z k := by
  simp [transferFactor, pow_add, h]

theorem transferProduct_period (z : F) (e r : ℕ) (h : z^e = 1) :
    transferProduct z (e*r) = transferProduct z e ^ r :=
  orderedProduct_period _ _ (transferFactor_period z e h) r

theorem denominator_period (z : F) (e r : ℕ) (h : z^e = 1) :
    denominator z (e*r) = denominator z e ^ r := by
  exact orderedProduct_period _ _ (fun k => by simp [pow_add, h]) r

theorem transferProduct_det (z : F) (r : ℕ) :
    (transferProduct z r).det = (Polynomial.C z)^r * (denominator z r)^2 := by
  induction r with
  | zero => simp [transferProduct, denominator, orderedProduct]
  | succ r ih =>
    change (transferProduct z r * transferFactor z r).det =
      (Polynomial.C z)^(r+1) * (denominator z r * (1-X*Polynomial.C (z^r)))^2
    rw [Matrix.det_mul, ih]
    unfold transferFactor
    rw [domino_det, pow_succ]
    ring

theorem period_det (z : F) (e : ℕ) (hz : z^e = 1) :
    (transferProduct z e).det = (denominator z e)^2 := by
  rw [transferProduct_det, ← map_pow, hz, map_one, one_mul]

/-- Formal division by a denominator with constant coefficient 1, without
introducing an infinite series or a division oracle. -/
def quotientCoeff (a d : Polynomial F) (m : ℕ) : F :=
  (Nat.rec (motive := fun _ => ℕ → F) (fun _ : ℕ => (0 : F))
    (fun r prev j => if j = r then
      a.coeff r - ∑ i : Fin r, d.coeff (r-i.val) * prev i.val
      else prev j) (m+1)) m

def parityCoefficient (e : ℕ) : ℤ := if e % 2 = 1 then 0 else 2 * (-1)^(e/2)

def universalTrace (e : ℕ) : Polynomial F :=
  2 + Polynomial.C (parityCoefficient e : F) * X^e

def universalDenominator (e : ℕ) : Polynomial F := 1-X^e

variable (n : ℕ) [NeZero n]
noncomputable def frequencyRoot (k : ZMod n) : CountingField n := (countingChar n).char (-k)

theorem frequencyRoot_pow (k : ZMod n) :
    frequencyRoot n k ^ addOrderOf k = 1 := by
  rw [frequencyRoot, ← AddChar.map_nsmul_eq_pow, smul_neg,
    addOrderOf_nsmul_eq_zero, neg_zero, AddChar.map_zero_eq_one]

theorem frequency_order_dvd (k : ZMod n) : addOrderOf k ∣ n := by
  simpa using (addOrderOf_dvd_card (x := k))

theorem frequency_product (k : ZMod n) :
    transferProduct (frequencyRoot n k) n =
      transferProduct (frequencyRoot n k) (addOrderOf k) ^ (n / addOrderOf k) := by
  conv_lhs => arg 2; rw [← Nat.mul_div_cancel' (frequency_order_dvd n k)]
  exact transferProduct_period _ _ _ (frequencyRoot_pow n k)

/-- OPEN: the inclusion-exclusion/closed-walk correspondence for the literal
frozen CycleTest count. Positive degree avoids the two empty constant rotors. -/
def TransferCountEvaluation : Prop :=
  ∀ (n m : ℕ) [NeZero n], 3 ≤ n → 1 ≤ m → ∀ k : ZMod n,
    finiteFourier (countingChar n).char (countVector n m) k =
      quotientCoeff (transferProduct (frequencyRoot n k) n).trace
        (denominator (frequencyRoot n k) n) m

/-- OPEN: the one-period polynomial trace and determinant, and root product.
No assertion about configuration counts is hidden in this obligation. -/
def PrimitivePeriodData : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ k : ZMod n,
    let e := addOrderOf k
    let z := frequencyRoot n k
    (transferProduct z e).trace = universalTrace e ∧
    denominator z e = universalDenominator e

theorem transfer_quotient_eq (hp : PrimitivePeriodData) (hn : 3 ≤ n)
    (k : ZMod n) (m : ℕ) :
    quotientCoeff (transferProduct (frequencyRoot n k) n).trace
      (denominator (frequencyRoot n k) n) m =
    quotientCoeff
      (lucasTrace (universalTrace (addOrderOf k))
        ((universalDenominator (addOrderOf k))^2) (n / addOrderOf k))
      ((universalDenominator (addOrderOf k))^(n / addOrderOf k)) m := by
  obtain ⟨ht, hg⟩ := hp n hn k
  have hd : (transferProduct (frequencyRoot n k) (addOrderOf k)).det =
      (universalDenominator (addOrderOf k))^2 := by
    rw [period_det _ _ (frequencyRoot_pow n k), hg]
  rw [frequency_product, trace_pow_eq_lucas, ht, hd]
  have he : denominator (frequencyRoot n k) n =
      (universalDenominator (addOrderOf k))^(n / addOrderOf k) := by
    conv_lhs => arg 2; rw [← Nat.mul_div_cancel' (frequency_order_dvd n k)]
    rw [denominator_period _ _ _ (frequencyRoot_pow n k), hg]
  rw [he]
end ChanLevine.Round3
