import MeanEExpansion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace LogArctangentMean
theorem E_jet_21 : iteratedDeriv 21 E 0 = 0 := by
  rw [E_eq_evalExpList, iteratedDeriv_evalExpList, expListJet_map]
  have hn (q : ExpQuadratic) : q.jet 21 = q.jetFormula 19 := q.jet_formula 19
  simp only [EList, pairExp, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, evalExpList, hn, ExpQuadratic.jetFormula, ExpQuadratic.eval, List.map_map, Function.comp_def]
  norm_num [Real.exp_zero, neg_pow]
  ring_nf
end LogArctangentMean
