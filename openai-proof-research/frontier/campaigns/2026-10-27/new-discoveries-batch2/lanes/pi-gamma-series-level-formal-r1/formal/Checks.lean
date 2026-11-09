import Mathlib
import GammaDefs
import SeriesDefect

set_option autoImplicit false
set_option warningAsError true

open GammaLevel

-- Definitions
#check @GammaLevel.seriesDefect
#check @GammaLevel.seriesDefectTail

-- (1) summability of terms
#check @GammaLevel.summable_seriesTerm
#check @GammaLevel.seriesTerm_nonneg
#check @GammaLevel.seriesTerm_le_inv_sq

-- (2) continuity
#check @GammaLevel.continuousOn_seriesDefect
#check @GammaLevel.continuousOn_seriesDefectTail

-- (3) strict antitonicity
#check @GammaLevel.strictAnti_seriesDefect
#check @GammaLevel.profile_strictAnti

-- (4) vanishing at +∞
#check @GammaLevel.seriesDefect_tendsto_zero
#check @GammaLevel.seriesDefectTail_tendsto_zero
#check @GammaLevel.seriesTerm_tendsto_zero

-- (5) divergence at the boundary
#check @GammaLevel.seriesDefect_tendsto_atTop
#check @GammaLevel.seriesTerm_zero_ge

-- (6) level existence / uniqueness (height statement)
#check @GammaLevel.exists_seriesDefect
#check @GammaLevel.existsUnique_seriesDefect
#check @GammaLevel.seriesDefect_eq

-- Axiom audit for every public declaration of this module
#print axioms GammaLevel.seriesDefect
#print axioms GammaLevel.seriesDefectTail
#print axioms GammaLevel.summable_seriesTerm
#print axioms GammaLevel.seriesTerm_nonneg
#print axioms GammaLevel.seriesTerm_le_inv_sq
#print axioms GammaLevel.continuousOn_seriesDefect
#print axioms GammaLevel.continuousOn_seriesDefectTail
#print axioms GammaLevel.strictAnti_seriesDefect
#print axioms GammaLevel.profile_strictAnti
#print axioms GammaLevel.seriesDefect_tendsto_zero
#print axioms GammaLevel.seriesDefectTail_tendsto_zero
#print axioms GammaLevel.seriesTerm_tendsto_zero
#print axioms GammaLevel.seriesDefect_tendsto_atTop
#print axioms GammaLevel.seriesTerm_zero_ge
#print axioms GammaLevel.exists_seriesDefect
#print axioms GammaLevel.existsUnique_seriesDefect
#print axioms GammaLevel.seriesDefect_eq
