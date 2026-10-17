/- Independent formal audit controls. Myeongjin Kang, MIT.
Concrete finite-set witnesses, not graph counterexamples. -/
import Controls
open scoped BigOperators
namespace SeymourReview

theorem threshold_zero (n : ℤ) :
    n^2 * (n^2+1) - (n^2+1) * ((n^2+1)-1) = 0 := by ring

theorem one_missing_zero (n : ℤ) :
    n^2 * (n^2+2) - (n^2+2) * ((n^2+2)-2) = 0 := by ring

theorem boundary_strict_hypothesis_needed :
    (-1 : ℤ) = 0 + 0 + 0 - 1 ∧ (-1 : ℤ) ≤ -1 ∧
    (1 : ℤ) ≤ 0+1 ∧ (0 : ℤ) ≤ 0 ∧ ¬((0 : ℤ) ≤ -1) := by norm_num

/-- The full aggregate hypotheses are simultaneously satisfiable, and sharp. -/
theorem realized_aggregate :
    (Finset.range 5 ⊆ Finset.range 12) ∧
    ((Finset.range 12).card : ℤ) = 2*6 ∧
    (6 : ℤ) = 2^2+2 ∧ (6-1 : ℤ) ≤ (Finset.range 5).card ∧
    (∀ i ∈ Finset.range 12 \ Finset.range 5,
       (if i < 5 then (-4 : ℤ) else 2) ≤ 2) ∧
    (∀ i ∈ Finset.range 5, (if i < 5 then (-4 : ℤ) else 2) ≤ 2-6) ∧
    (∑ i ∈ Finset.range 12, (if i < 5 then (-4 : ℤ) else 2)) = -6 := by
  refine ⟨Finset.range_mono (by omega), by norm_num, by norm_num,
    by norm_num, ?_, ?_, ?_⟩
  · intro i hi
    split_ifs <;> norm_num
  · intro i hi
    have h : i < 5 := Finset.mem_range.mp hi
    simp [h]
  · norm_num [Finset.sum_range_succ]

/-- Dropping disjointness fails for actual sets, not just formal cardinals. -/
theorem overlapping_sets_no_gain :
    let U : Finset (Fin 3) := Finset.univ
    let E : Finset (Fin 3) := ∅
    U ⊆ U ∧ E ⊆ U ∧ ¬Disjoint U U ∧
    U.card + E.card < 2*U.card ∧
    ¬(U.card + U.card + 2*(U \ (U ∪ U)).card <
        (U \ E).card + (U \ E).card) := by decide

/-- Weak pruning gain can preserve the objective exactly. -/
theorem nonstrict_gain_sets :
    let R := Finset.range 5
    let P := Finset.range 4
    P ⊆ R ∧ (6+2*2 : ℕ) ≤ R.card + R.card ∧
    (R \ P).card + (R \ P).card ≤ 2+0 ∧
    ¬((6+2 : ℕ) < P.card + P.card + 0) := by decide

/-- A genuine disjoint-image instance satisfies strict complement gain. -/
theorem complement_nonvacuous :
    let U := Finset.range 4
    let JP : Finset ℕ := {0,1}
    let JQ : Finset ℕ := {2,3}
    let P : Finset ℕ := {0}
    let Q : Finset ℕ := {3}
    let E : Finset ℕ := ∅
    JP ⊆ U ∧ JQ ⊆ U ∧ Disjoint JP JQ ∧
    P.card+E.card < 2*JP.card ∧ Q.card+E.card < 2*JQ.card ∧
    P.card+Q.card+2*(U \ (JP ∪ JQ)).card < (U \ E).card+(U \ E).card := by decide

end SeymourReview
#print axioms SeymourReview.threshold_zero
#print axioms SeymourReview.one_missing_zero
#print axioms SeymourReview.boundary_strict_hypothesis_needed
#print axioms SeymourReview.realized_aggregate
#print axioms SeymourReview.overlapping_sets_no_gain
#print axioms SeymourReview.nonstrict_gain_sets
#print axioms SeymourReview.complement_nonvacuous
