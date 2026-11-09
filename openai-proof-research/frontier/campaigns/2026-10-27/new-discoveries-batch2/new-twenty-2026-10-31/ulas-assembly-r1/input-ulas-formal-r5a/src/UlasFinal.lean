import UlasSeries
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Ulas
noncomputable def diff (m n : ℕ) : ℤ := c m (4*n) - c m n
noncomputable def val (m n : ℕ) : ℕ := padicValInt 2 (diff m n)
def targetEven (k n : ℕ) : ℕ := padicValNat 2 n + 2*padicValNat 2 k + 3

def EvenFormula : Prop := ∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
  diff (2*k) n ≠ 0 ∧ val (2*k) n = targetEven k n
def OddOneBound : Prop := ∀ k n : ℕ, 1 ≤ n →
  diff (4*k+1) n ≠ 0 ∧ padicValNat 2 n + 3 ≤ val (4*k+1) n
def OddThreeBound : Prop := ∀ k n : ℕ, 1 ≤ n →
  diff (4*k+3) n ≠ 0 ∧ padicValNat 2 n + 6 ≤ val (4*k+3) n
noncomputable def evenEq (k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ val (2*k) n = targetEven k n}
noncomputable def oddEq (k a : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ val (4*k+a) n = padicValNat 2 n + (if a = 1 then 3 else 6)}

/-- Literal per-colour reading of Conjecture 6.1. -/
def Conj61 : Prop := EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧
  (∀ k, 1 ≤ k → (evenEq k).Infinite) ∧
  (∀ k, (oddEq k 1).Infinite) ∧ (∀ k, (oddEq k 3).Infinite)
/-- Some-colour reading: bounds stay universal, sharpness is existential in k. -/
def Conj61Some : Prop := EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧
  (∃ k, 1 ≤ k ∧ (evenEq k).Infinite) ∧
  (∃ k, (oddEq k 1).Infinite) ∧ (∃ k, (oddEq k 3).Infinite)

/-- Remaining universal parity readout for colours 1 modulo 4. -/
def OddOneEquality : Prop := ∀ k n : ℕ, 1 ≤ n → n % 2 = 1 →
  val (4*k+1) n = padicValNat 2 n + 3
/-- These are sufficient sets; the manuscript does not claim an iff. -/
def OddThreeEquality : Prop := ∀ k n : ℕ, 1 ≤ n →
  (((4*k+3)%16 = 3 ∨ (4*k+3)%16 = 7) ∧ n%2 = 1 ∨
   (4*k+3)%16 = 11 ∧ n%4 = 2) →
  val (4*k+3) n = padicValNat 2 n + 6
/-- Stronger bound on the entire residue class, not just m = 15. -/
def FifteenBound : Prop := ∀ t n : ℕ, 1 ≤ n →
  diff (16*t+15) n ≠ 0 ∧ padicValNat 2 n + 7 ≤ val (16*t+15) n

/-- EXACT remaining obligations of this round; no inhabitant is postulated. -/
def Remaining : Prop := EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧
  OddOneEquality ∧ OddThreeEquality ∧ FifteenBound

def NeverFifteen : Prop := ∀ t n : ℕ, 1 ≤ n →
  val (16*t+15) n ≠ padicValNat 2 n + 6

theorem never_fifteen (h : FifteenBound) : NeverFifteen := by
  intro t n hn he
  have hh := (h t n hn).2
  rw [he] at hh
  omega

/-- CONDITIONAL full manuscript theorem, including the universal never clause. -/
theorem full_theorem (h : Remaining) :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
   h.2.2.2.2.2, never_fifteen h.2.2.2.2.2⟩

/-- CONDITIONAL literal refutation; all remaining mathematics is an explicit argument. -/
theorem mathdb_342364 (h : Remaining) : ¬ Conj61 := by
  intro hc
  obtain ⟨n, hn, _⟩ := (hc.2.2.2.2.2 3).exists_gt 0
  have hd := never_fifteen h.2.2.2.2.2 0 n hn.1
  exact hd (by simpa [oddEq] using hn.2)

/-- CONDITIONAL proof of the alternative reading with k = 1, 0, 0. -/
theorem conj61_some (h : Remaining) : Conj61Some := by
  refine ⟨h.1, h.2.1, h.2.2.1, ⟨1, by omega, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · apply Set.infinite_of_forall_exists_gt
    intro a
    exact ⟨a+1, ⟨by omega, (h.1 1 (a+1) (by omega) (by omega)).2⟩, by omega⟩
  · apply Set.infinite_of_forall_exists_gt
    intro a
    refine ⟨2*a+1, ⟨by omega, ?_⟩, by omega⟩
    simpa [oddEq] using h.2.2.2.1 0 (2*a+1) (by omega) (by omega)
  · apply Set.infinite_of_forall_exists_gt
    intro a
    refine ⟨2*a+1, ⟨by omega, ?_⟩, by omega⟩
    simpa [oddEq] using h.2.2.2.2.1 0 (2*a+1) (by omega) (by omega)
end Ulas
