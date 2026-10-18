import T224G

namespace T224GControls

-- The mixed old-state indicator is necessary even under both sandwiches.
theorem mixed_old_nonvacuous :
    T224G.Sandwich false false true ∧ T224G.Sandwich false true true := by
  simp [T224G.Sandwich]

theorem mixed_old_product_zero :
    ((T224G.bit false - T224G.bit false) * (T224G.bit false - T224G.bit true) +
      (T224G.bit true - T224G.bit false) * (T224G.bit true - T224G.bit true)) / 2 = 0 := by
  norm_num [T224G.bit]

theorem omit_indicator_false :
    (0 : ℝ) ≠ T224G.pivotal false true * T224G.pivotal false true / 2 := by
  norm_num [T224G.pivotal, T224G.bit]

-- f(u,v)=v has zero mixed coefficient but a nonzero birth drift.
theorem omit_drift_false :
    T224G.birthDifference (fun _ v => T224G.bit v) false false true ≠
      T224G.refreshDifference (fun _ v => T224G.bit v) false true := by
  norm_num [T224G.birthDifference, T224G.refreshDifference, T224G.bit]

-- f(u,v)=u*v witnesses the half mixed-coefficient correction.
theorem omit_half_mixed_drift_false :
    T224G.birthDifference (fun u v => T224G.bit u * T224G.bit v) false false true ≠
      - T224G.mixedCoefficient (fun u v => T224G.bit u * T224G.bit v) *
        T224G.pivotal false true / 4 := by
  norm_num [T224G.birthDifference, T224G.mixedCoefficient, T224G.pivotal, T224G.bit]

theorem omit_replica_cross_term_false :
    (2 : ℝ) * 2 - 1 ≠ (2 - 1) + (2 - 1) := by norm_num

-- Deleting the sandwich hypothesis genuinely breaks the identity.
theorem no_sandwich_counterexample :
    T224G.birthDifference (fun u v => T224G.bit u * T224G.bit v) true false false ≠
      (0 + T224G.mixedCoefficient (fun u v => T224G.bit u * T224G.bit v) / 2) *
        T224G.drift true false false -
      T224G.mixedCoefficient (fun u v => T224G.bit u * T224G.bit v) *
        T224G.pivotal true false / 4 := by
  norm_num [T224G.birthDifference, T224G.mixedCoefficient, T224G.drift,
    T224G.pivotal, T224G.bit]

end T224GControls
