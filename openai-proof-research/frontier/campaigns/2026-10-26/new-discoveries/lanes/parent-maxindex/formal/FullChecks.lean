import ScalarBounds
import FiniteSelections
import CoefficientBounds
import GeometricBounds
import IncidenceBounds
import ProbabilityEntries
import ArithmeticHigh
import SortedBridge
import UniversalBound
import Sharpness
import Reindexing
import SourceClassification

#check MaxIndex.low_maximum_bound
#print axioms MaxIndex.low_maximum_bound
#check MaxIndex.high_maximum_bound
#print axioms MaxIndex.high_maximum_bound
#check MaxIndex.sharpness_gap_positive
#print axioms MaxIndex.sharpness_gap_positive
#check MaxIndex.sharpness_selected_sum
#print axioms MaxIndex.sharpness_selected_sum
#check MaxIndex.selectionFamily
#print axioms MaxIndex.selectionFamily
#check MaxIndex.mem_selectionFamily
#print axioms MaxIndex.mem_selectionFamily
#check MaxIndex.selectionFamily_nonempty
#print axioms MaxIndex.selectionFamily_nonempty
#check MaxIndex.maskTopSum
#print axioms MaxIndex.maskTopSum
#check MaxIndex.selected_sum_le_maskTopSum
#print axioms MaxIndex.selected_sum_le_maskTopSum
#check MaxIndex.maskTopSum_le
#print axioms MaxIndex.maskTopSum_le
#check MaxIndex.maskTopSum_nonneg
#print axioms MaxIndex.maskTopSum_nonneg
#check MaxIndex.exists_maskTopSum
#print axioms MaxIndex.exists_maskTopSum
#check MaxIndex.maskTopSum_mono
#print axioms MaxIndex.maskTopSum_mono
#check MaxIndex.exists_full_maskTopSum
#print axioms MaxIndex.exists_full_maskTopSum
#check MaxIndex.exists_full_maskTopSum_containing
#print axioms MaxIndex.exists_full_maskTopSum_containing
#check MaxIndex.weighted_coefficient_bound
#print axioms MaxIndex.weighted_coefficient_bound
#check MaxIndex.selected_sum_sq_le_card
#print axioms MaxIndex.selected_sum_sq_le_card
#check MaxIndex.selected_sum_le_sqrt
#print axioms MaxIndex.selected_sum_le_sqrt
#check MaxIndex.maskTopSum_le_sqrt
#print axioms MaxIndex.maskTopSum_le_sqrt
#check MaxIndex.maskTopSum_le_head_sqrt
#print axioms MaxIndex.maskTopSum_le_head_sqrt
#check MaxIndex.edgeDegree
#print axioms MaxIndex.edgeDegree
#check MaxIndex.incidence
#print axioms MaxIndex.incidence
#check MaxIndex.arithmeticEntry
#print axioms MaxIndex.arithmeticEntry
#check MaxIndex.geometricEntry
#print axioms MaxIndex.geometricEntry
#check MaxIndex.sum_arithmetic_eq_incidence
#print axioms MaxIndex.sum_arithmetic_eq_incidence
#check MaxIndex.edgeDegree_le
#print axioms MaxIndex.edgeDegree_le
#check MaxIndex.incidence_le
#print axioms MaxIndex.incidence_le
#check MaxIndex.edgeDegree_pair_le
#print axioms MaxIndex.edgeDegree_pair_le
#check MaxIndex.incidence_pair_le
#print axioms MaxIndex.incidence_pair_le
#check MaxIndex.arithmetic_low_maximum
#print axioms MaxIndex.arithmetic_low_maximum
#check MaxIndex.probability_le_one
#print axioms MaxIndex.probability_le_one
#check MaxIndex.probability_tail_le
#print axioms MaxIndex.probability_tail_le
#check MaxIndex.geometricEntry_nonneg
#print axioms MaxIndex.geometricEntry_nonneg
#check MaxIndex.geometricEntry_sq
#print axioms MaxIndex.geometricEntry_sq
#check MaxIndex.geometricEntry_unit
#print axioms MaxIndex.geometricEntry_unit
#check MaxIndex.geometricEntry_diagonal
#print axioms MaxIndex.geometricEntry_diagonal
#check MaxIndex.geometricEntry_le_maximum
#print axioms MaxIndex.geometricEntry_le_maximum
#check MaxIndex.geometric_low_bound
#print axioms MaxIndex.geometric_low_bound
#check MaxIndex.geometric_high_bound
#print axioms MaxIndex.geometric_high_bound
#check MaxIndex.arithmetic_high_pointwise
#print axioms MaxIndex.arithmetic_high_pointwise
#check MaxIndex.arithmetic_high_sum
#print axioms MaxIndex.arithmetic_high_sum
#check MaxIndex.sum_le_top_selection
#print axioms MaxIndex.sum_le_top_selection
#check MaxIndex.descendingIndices
#print axioms MaxIndex.descendingIndices
#check MaxIndex.descendingIndices_perm
#print axioms MaxIndex.descendingIndices_perm
#check MaxIndex.descendingIndices_nodup
#print axioms MaxIndex.descendingIndices_nodup
#check MaxIndex.descendingIndices_mem
#print axioms MaxIndex.descendingIndices_mem
#check MaxIndex.descendingIndices_length
#print axioms MaxIndex.descendingIndices_length
#check MaxIndex.descendingIndices_pairwise
#print axioms MaxIndex.descendingIndices_pairwise
#check MaxIndex.sortedTopSum
#print axioms MaxIndex.sortedTopSum
#check MaxIndex.sortedTopSum_eq_maskTopSum
#print axioms MaxIndex.sortedTopSum_eq_maskTopSum
#check MaxIndex.universal_mask_bound
#print axioms MaxIndex.universal_mask_bound
#check MaxIndex.source_universal_index
#print axioms MaxIndex.source_universal_index
#check MaxIndex.WitnessIndex
#print axioms MaxIndex.WitnessIndex
#check MaxIndex.witnessRadius
#print axioms MaxIndex.witnessRadius
#check MaxIndex.witnessDenominator
#print axioms MaxIndex.witnessDenominator
#check MaxIndex.witnessProbability
#print axioms MaxIndex.witnessProbability
#check MaxIndex.witnessDenominator_pos
#print axioms MaxIndex.witnessDenominator_pos
#check MaxIndex.witnessProbability_nonneg
#print axioms MaxIndex.witnessProbability_nonneg
#check MaxIndex.witnessProbability_sum
#print axioms MaxIndex.witnessProbability_sum
#check MaxIndex.starMask
#print axioms MaxIndex.starMask
#check MaxIndex.starMask_disjoint
#print axioms MaxIndex.starMask_disjoint
#check MaxIndex.starMask_card
#print axioms MaxIndex.starMask_card
#check MaxIndex.arithmeticWitnessMask
#print axioms MaxIndex.arithmeticWitnessMask
#check MaxIndex.geometricWitnessMask
#print axioms MaxIndex.geometricWitnessMask
#check MaxIndex.arithmeticWitnessMask_card
#print axioms MaxIndex.arithmeticWitnessMask_card
#check MaxIndex.geometricWitnessMask_card
#print axioms MaxIndex.geometricWitnessMask_card
#check MaxIndex.sum_starMask
#print axioms MaxIndex.sum_starMask
#check MaxIndex.witness_geometric_star
#print axioms MaxIndex.witness_geometric_star
#check MaxIndex.witness_arithmetic_selected_sum
#print axioms MaxIndex.witness_arithmetic_selected_sum
#check MaxIndex.witness_geometric_selected_sum
#print axioms MaxIndex.witness_geometric_selected_sum
#check MaxIndex.witness_next_index_fails
#print axioms MaxIndex.witness_next_index_fails
#check MaxIndex.maskTopSum_reindex_le
#print axioms MaxIndex.maskTopSum_reindex_le
#check MaxIndex.maskTopSum_comp_equiv
#print axioms MaxIndex.maskTopSum_comp_equiv
#check MaxIndex.sortedTopSum_mono
#print axioms MaxIndex.sortedTopSum_mono
#check MaxIndex.source_next_index_counterexample
#print axioms MaxIndex.source_next_index_counterexample
#check MaxIndex.source_index_classification
#print axioms MaxIndex.source_index_classification
