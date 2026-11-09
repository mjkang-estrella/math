import CountR6Rotor
import CountR6Quotient
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round6
open Polynomial Round3
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F]

/-- Finite cyclic matching polynomial after clearing the geometric denominators. -/
def matchingNumerator (n : ℕ) [NeZero n] (z : F) : Polynomial F :=
  ∑ s ∈ (Finset.univ : Finset (ZMod n)).powerset,
    if Matching s then
      (Polynomial.C (-z))^s.card * (Polynomial.C (1+z))^(n-2*s.card) *
        ∏ v ∈ s ∪ rightEnds s, (1-X*Polynomial.C (z^v.val))
    else 0

/-- Degree zero counts the two empty constant rotors. Positive levels retain
exactly the frozen Fourier count. -/
def completedFourier (n : ℕ) [NeZero n] (k : ZMod n) (m : ℕ) : CountingField n :=
  if m = 0 then 2 else finiteFourier (countingChar n).char (countVector n m) k

/-- OPEN: chip-function summation and clearing the denominator. The zero
coefficient explicitly includes the two excluded empty constant rotors. -/
def MatchingCountConvolution : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (k : ZMod n) (m : ℕ),
    (matchingNumerator n (frequencyRoot n k)).coeff m =
      ∑ i : Fin (m+1), (denominator (frequencyRoot n k) n).coeff (m-i.val) *
        completedFourier n k i.val

/-- OPEN: ordered closed-state expansion with all cyclic matchings,
including wrap edges and both alternating perfect matchings. -/
def MatchingTraceExpansion : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ k : ZMod n,
    (transferProduct (frequencyRoot n k) n).trace =
      matchingNumerator n (frequencyRoot n k)

/-- The literal frozen remaining bridge follows from these two finite identities. -/
theorem transferCountEvaluation (hc : MatchingCountConvolution)
    (ht : MatchingTraceExpansion) : TransferCountEvaluation := by
  intro n m inst hn hm k
  have hq := quotientCoeff_of_convolution
    (matchingNumerator n (frequencyRoot n k)) (denominator (frequencyRoot n k) n)
    (denominator_constant _ _) (completedFourier n k) (hc n hn k) m
  rw [ht n hn k, hq]
  simp [completedFourier, show m ≠ 0 by omega]
end ChanLevine.Round6
