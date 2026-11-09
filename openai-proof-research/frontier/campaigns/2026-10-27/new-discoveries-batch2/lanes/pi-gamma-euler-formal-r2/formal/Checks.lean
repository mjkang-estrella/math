import GammaEuler
import GammaRatio

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open Set Filter Topology

namespace GammaLevel

-- Interface checks: exact types of every new declaration.

#check @GammaLevel.finite_sum_eq_logGammaSeq
#check @GammaLevel.tendsto_logGammaSeq_mix
#check @GammaLevel.tendsto_partialSum_logDefect
#check @GammaLevel.seriesTerm_nonneg
#check @GammaLevel.gammaHasSum
#check @GammaLevel.gammaHasSum'
#check @GammaLevel.logDefect_shift
#check @GammaLevel.logDefect_eq_log_iff_ratio
#check @GammaLevel.sourceLevel_iff_defect

-- Axiom audit for every new declaration.
#print axioms GammaLevel.finite_sum_eq_logGammaSeq
#print axioms GammaLevel.tendsto_logGammaSeq_mix
#print axioms GammaLevel.tendsto_partialSum_logDefect
#print axioms GammaLevel.seriesTerm_nonneg
#print axioms GammaLevel.gammaHasSum
#print axioms GammaLevel.gammaHasSum'
#print axioms GammaLevel.logDefect_shift
#print axioms GammaLevel.logDefect_eq_log_iff_ratio
#print axioms GammaLevel.sourceLevel_iff_defect

-- Downstream usability: the exact hypothesis shapes the root assembly consumes.
#check fun (x s : ℝ) (hx : 0 < x) (hsx : x < s) => GammaLevel.gammaHasSum hx hsx
#check fun (c x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hc : 0 < c) =>
  GammaLevel.logDefect_eq_log_iff_ratio hx hy hc

end GammaLevel
