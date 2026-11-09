import FiniteProbability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option autoImplicit false
set_option linter.style.haveILetI false
namespace LiteralGame
attribute [local instance] Classical.propDecidable

theorem coordinate_measurable (N : ℕ) (I : Set ℕ) (i : ℕ) (hi : i ∈ I) :
    @Measurable (Outcome N) ℕ (coordinateSigma N I) ⊤ (fun w => X w i) := by
  apply measurable_iff_comap_le.mpr
  unfold coordinateSigma
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

theorem termination_measurable (N m : ℕ) :
    (prefixSigma N m).MeasurableSet' {w | w.val.length < m} := by
  letI : MeasurableSpace (Outcome N) := prefixSigma N m
  have hx (j : ℕ) (hj : j ∈ Finset.range m) : Measurable (fun w : Outcome N => X w (j+1)) := by
    exact coordinate_measurable N _ _ (by simp only [Set.mem_Icc,Finset.mem_range] at *; omega)
  have hs : Measurable (fun w : Outcome N => ∑ j ∈ Finset.range m, X w (j+1)) :=
    Finset.measurable_sum _ hx
  have hm : MeasurableSet {w : Outcome N | N-Z N < m-(∑ j ∈ Finset.range m, X w (j+1))} :=
    hs (show MeasurableSet {x : ℕ | N-Z N < m-x} from trivial)
  have he : {w : Outcome N | w.val.length < m} =
      {w : Outcome N | N-Z N < m-(∑ j ∈ Finset.range m, X w (j+1))} := by
    ext w
    exact prefix_observable w.property m
  rw [he]
  exact hm

theorem lastSplit_measurable (N r : ℕ) (hr : 1≤r) :
    (suffixSigma N r).MeasurableSet' {w | r ≤ lastSplit w.val} := by
  letI : MeasurableSpace (Outcome N) := suffixSigma N r
  have he : {w : Outcome N | r ≤ lastSplit w.val} =
      ⋃ i : ℕ, ⋃ (_ : i ∈ Finset.Icc r (duration N)), {w | X w.val i = 1} := by
    ext w
    simpa using suffix_observable_finite w.property r hr
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro hi
  have hx : Measurable (fun w : Outcome N => X w.val i) :=
    coordinate_measurable N _ i (by simpa using hi)
  exact measurableSet_eq_fun hx measurable_const

theorem disjoint_stopping_events (N m k : ℕ) (hk : 1≤k) :
    Disjoint {w : Outcome N | w.val.length < m} {w | m+k ≤ lastSplit w.val} := by
  apply Set.disjoint_left.mpr
  intro w ha hb
  have := lastSplit_le w.val
  change w.val.length < m at ha
  change m+k ≤ lastSplit w.val at hb
  omega

end LiteralGame
