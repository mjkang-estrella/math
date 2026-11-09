import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
namespace DualPolar
open Finset

/-- Literal Gaussian binomial product over Q; zero outside its support. -/
def gaussian (q n k : ℕ) : ℚ :=
  if k ≤ n then ∏ h ∈ range k,
    (((q : ℚ) ^ (n-h) - 1) / ((q : ℚ) ^ (k-h) - 1)) else 0

/-- Section 6 displayed eigenvalue formula with qe = q^e. -/
def C (q qe d j i : ℕ) : ℚ :=
  ∑ h ∈ range (i+1), if i-j ≤ h ∧ h ≤ min (d-j) i then
    (-1 : ℚ) ^ (i-h) * (q : ℚ) ^ ((i-h)*(i-h-1)/2 + (j-(i-h))*(j-(i-h)-1)/2) *
    (qe : ℚ) ^ (j-(i-h)) * gaussian q (d-i) (d-j-h) * gaussian q i h
    else 0

def magnitude (q qe d j i : ℕ) : ℚ := |C q qe d j i|
def minimumAt (q qe d j i : ℕ) : Prop :=
  i ≤ d ∧ ∀ k ∈ range (d+1), magnitude q qe d j i ≤ magnitude q qe d j k

def valley (q qe d j : ℕ) : Prop := ∃ m ∈ range (d+1),
  (∀ i ∈ range (m+1), ∀ k ∈ range (m+1), i ≤ k →
    magnitude q qe d j k ≤ magnitude q qe d j i) ∧
  (∀ i ∈ range (d+1), ∀ k ∈ range (d+1), m ≤ i → i ≤ k →
    magnitude q qe d j i ≤ magnitude q qe d j k)

def primePower (q : ℕ) : Prop := ∃ p s : ℕ, p.Prime ∧ 0 < s ∧ q = p^s
/-- e2 is twice the source parameter e. -/
def admissible (q qe e2 : ℕ) : Prop := primePower q ∧
  ((e2=0 ∧ qe=1) ∨ (e2=2 ∧ qe=q) ∨ (e2=4 ∧ qe=q^2) ∨
   (∃ r : ℕ, primePower r ∧ q=r^2 ∧ ((e2=1 ∧ qe=r) ∨ (e2=3 ∧ qe=r^3))))

def location (q qe e2 d j : ℕ) : Prop := ∃ i ∈ range (d+1),
  minimumAt q qe d j i ∧
  (if (q,e2,j,d) = (2,2,3,4) ∨ (q,e2,j,d) = (2,4,3,7) then
     i+2 = (2*d+e2+2)/4
   else if e2=0 ∨ e2=1 ∨ e2=3 then i=(2*d+e2+2)/4
   else i ≤ (2*d+e2+2)/4+1 ∧ (2*d+e2+2)/4 ≤ i+1)

/-- Conjecture 6.2, with the weakest existential reading of tied minima. -/
def SourceFormulaConjecture : Prop := ∀ q qe e2 d j : ℕ,
  admissible q qe e2 → 1 ≤ j → j ≤ d →
  (((q,e2) ≠ (2,2) ∧ ¬(q=2 ∧ e2=4 ∧ j=d-4 ∧ 8 ≤ d ∧ d ≤ 12) → valley q qe d j) ∧
   (valley q qe d j → location q qe e2 d j))

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem column : (List.range 5).map (C 4 8 4 2) = [91392,5208,60,-84,1428] := by
  norm_num [List.range_succ, C, gaussian, Finset.sum_range_succ, Finset.prod_range_succ]

theorem witness_valley : valley 4 8 4 2 := by
  refine ⟨2, by decide, ?_⟩
  constructor
  · intro i hi k hk hik
    simp only [Finset.mem_range] at hi hk
    interval_cases i <;> interval_cases k <;>
      norm_num [magnitude, C, gaussian, Finset.sum_range_succ, Finset.prod_range_succ] at *
  · intro i hi k hk hmi hik
    simp only [Finset.mem_range] at hi hk
    interval_cases i <;> interval_cases k <;>
      norm_num [magnitude, C, gaussian, Finset.sum_range_succ, Finset.prod_range_succ] at *

theorem location_fails : ¬ location 4 8 3 4 2 := by
  rintro ⟨i, _, hmin, hidx⟩
  have hi3 : i=3 := by simpa using hidx
  subst i
  have hh := hmin.2 2 (by decide)
  norm_num [magnitude, C, gaussian, Finset.sum_range_succ, Finset.prod_range_succ] at hh

theorem witness_admissible : admissible 4 8 3 := by
  refine ⟨⟨2,2,by norm_num,by decide,by decide⟩, Or.inr (Or.inr (Or.inr ?_))⟩
  exact ⟨2, ⟨2,1,by norm_num,by decide,by decide⟩, by decide, Or.inr ⟨rfl,rfl⟩⟩

theorem source_formula_refuted : ¬ SourceFormulaConjecture := by
  intro h
  exact location_fails ((h 4 8 3 4 2 witness_admissible (by decide) (by decide)).2 witness_valley)

#print axioms gaussian
#print axioms C
#print axioms magnitude
#print axioms minimumAt
#print axioms valley
#print axioms primePower
#print axioms admissible
#print axioms location
#print axioms SourceFormulaConjecture
#print axioms column
#print axioms witness_valley
#print axioms location_fails
#print axioms witness_admissible
#print axioms source_formula_refuted
end DualPolar
