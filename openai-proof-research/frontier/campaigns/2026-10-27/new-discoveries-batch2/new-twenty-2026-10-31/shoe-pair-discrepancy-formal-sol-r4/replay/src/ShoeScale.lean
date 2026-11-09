import ShoeBlockSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace Shoe
open MeasureTheory
open scoped ENNReal

noncomputable def realMass (p : DiscreteLaw ℕ) : ℝ := (collisionMass p).toReal
noncomputable def realProb (p : DiscreteLaw ℕ) (i : ℕ) : ℝ := (p i).toReal

theorem realMass_pos (p : DiscreteLaw ℕ) : 0 < realMass p :=
  ENNReal.toReal_pos (collisionMass_ne_zero p) (collisionMass_ne_top p)

theorem realMass_le_one (p : DiscreteLaw ℕ) : realMass p ≤ 1 := by
  simpa [realMass] using ENNReal.toReal_mono ENNReal.one_ne_top (collisionMass_le_one p)

theorem realProb_nonneg (p : DiscreteLaw ℕ) (i : ℕ) : 0 ≤ realProb p i :=
  ENNReal.toReal_nonneg

theorem realProb_le_one (p : DiscreteLaw ℕ) (i : ℕ) : realProb p i ≤ 1 := by
  simpa [realProb] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one i)

theorem realProb_sq_le (p : DiscreteLaw ℕ) (i : ℕ) : (realProb p i)^2 ≤ realMass p := by
  have h := ENNReal.toReal_mono (collisionMass_ne_top p)
    (ENNReal.le_tsum (f := fun j => p j * p j) i)
  simpa [realMass, realProb, collisionMass, ENNReal.toReal_mul, pow_two] using h

theorem realProb_le_sqrt (p : DiscreteLaw ℕ) (i : ℕ) :
    realProb p i ≤ Real.sqrt (realMass p) := by
  have hsq := Real.sq_sqrt (le_of_lt (realMass_pos p))
  have hn := Real.sqrt_nonneg (realMass p)
  have hp := realProb_sq_le p i
  nlinarith [realProb_nonneg p i]

theorem bernoulli_complement (t : ℝ) (_ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    1 - (n : ℝ)*t ≤ (1-t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr ht1)
    have hn : 0 ≤ (n : ℝ)*t^2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg t)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

noncomputable def blockSize (p : DiscreteLaw ℕ) : ℕ :=
  ⌊1/(4*Real.sqrt (realMass p))⌋₊

theorem blockSize_scale (p : DiscreteLaw ℕ) (hs : realMass p < 1/64) :
    2 ≤ blockSize p ∧
    1/(8*Real.sqrt (realMass p)) ≤ (blockSize p : ℝ) ∧
    (blockSize p : ℝ)*Real.sqrt (realMass p) ≤ 1/4 ∧
    (blockSize p : ℝ)^2 * realMass p ≤ 1/16 ∧
    1/(64*realMass p) ≤ (blockSize p : ℝ)^2 := by
  have hmass := realMass_pos p
  let r := Real.sqrt (realMass p)
  have hr : 0 < r := Real.sqrt_pos.mpr (realMass_pos p)
  have hrr : r^2 = realMass p := Real.sq_sqrt (le_of_lt (realMass_pos p))
  have hr8 : r < 1/8 := by nlinarith
  have hu : 2 < 1/(4*r) := (lt_div_iff₀ (by positivity)).2 (by nlinarith)
  have hlow := Nat.lt_floor_add_one (1/(4*r))
  have hu0 : 0 ≤ 1/(4*r) := by positivity
  have hhigh := Nat.floor_le hu0
  change 1/(4*r) < (blockSize p : ℝ)+1 at hlow
  change (blockSize p : ℝ) ≤ 1/(4*r) at hhigh
  have hk2 : 2 ≤ blockSize p := Nat.le_floor (le_of_lt hu)
  have hk : (blockSize p : ℝ)*r ≤ 1/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*r)).mp hhigh
    nlinarith
  have hl : 1/(8*r) ≤ (blockSize p : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 8*r)).2
    have hh := (div_lt_iff₀ (by positivity : 0 < 4*r)).mp hlow
    nlinarith
  refine ⟨hk2,hl,hk,?_,?_⟩
  · nlinarith [sq_nonneg ((blockSize p : ℝ)*r-1/4),
      mul_nonneg (Nat.cast_nonneg (blockSize p)) hr.le]
  · apply (div_le_iff₀ (by positivity : 0 < 64*realMass p)).2
    have hh := (div_le_iff₀ (by positivity : 0 < 8*r)).mp hl
    nlinarith [sq_nonneg ((blockSize p : ℝ)*r-1/8)]

end Shoe
