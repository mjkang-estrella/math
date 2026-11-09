import UlasParity
import UlasLow

open PowerSeries
namespace Ulas.Round2
/-- Full-series numerator of the iterated difference, prior to polynomial reduction. -/
noncomputable def transferDiff (m j : ℕ) : PowerSeries ℤ :=
  transferIter m (j+2) - transferIter m j

theorem transferDiff_succ (m j : ℕ) :
    transferDiff m (j+1) = sectionEven (w^m * transferDiff m j) := by
  simp only [transferDiff, transferIter, mul_sub, sectionEven_sub]

/-- Equation (1) with the faithful coefficient definition for arbitrary j and n. -/
theorem diff_readout (m j n : ℕ) :
    diff m (2^j*n) = coeff n (C^m * transferDiff m j) := by
  unfold diff transferDiff
  rw [show 4*(2^j*n) = 2^(j+2)*n by ring, c_transfer, c_transfer,
    mul_sub, map_sub]

/-- The exact six open obligations, inherited byte-for-byte from round 1. -/
def Remaining : Prop := Ulas.Remaining

/-- Conditional endpoint; this round does not supply Remaining. -/
theorem full_theorem (h : Remaining) :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen := Ulas.full_theorem h

theorem mathdb_342364 (h : Remaining) : ¬ Conj61 := Ulas.mathdb_342364 h

theorem conj61_some (h : Remaining) : Conj61Some := Ulas.conj61_some h
end Ulas.Round2
