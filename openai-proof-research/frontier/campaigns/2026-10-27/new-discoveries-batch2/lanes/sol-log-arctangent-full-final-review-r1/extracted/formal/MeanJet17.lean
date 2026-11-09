import MeanEExpansion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace LogArctangentMean
theorem E_jet_17 : iteratedDeriv 17 E 0 = 0 := by
  rw [E_eq_evalExpList, iteratedDeriv_evalExpList, expListJet_map]
  have hn (q : ExpQuadratic) : q.jet 17 = q.jetFormula 15 := q.jet_formula 15
  simp only [EList, pairExp, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, evalExpList, hn, ExpQuadratic.jetFormula, ExpQuadratic.eval, List.map_map, Function.comp_def]
  norm_num [Real.exp_zero]
  dsimp [freq0, u0, v0, freq1, u1, v1, freq2, u2, v2, freq3, u3, v3, freq4, u4, v4, freq5, u5, v5, freq6, u6, v6, freq7, u7, v7, freq8, u8, v8, freq9, u9, v9, freq10, u10, v10, freq11, u11, v11]
  ring_nf
  all_goals simp only [d_power_2, d_power_3, d_power_4, d_power_5, d_power_6, d_power_7, d_power_8, d_power_9, d_power_10, d_power_11, d_power_12, d_power_13, d_power_14, d_power_15, d_power_16, d_power_17, d_power_18, d_power_19, d_power_20, d_power_21, d_power_22, d_power_23, d_power_24, d_power_25, d_power_26]; ring
end LogArctangentMean
