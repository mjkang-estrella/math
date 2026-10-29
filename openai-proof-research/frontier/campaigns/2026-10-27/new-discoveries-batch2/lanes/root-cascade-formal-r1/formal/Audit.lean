import SelectedCounting
set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
#check CascadeRate.depth
#print axioms CascadeRate.depth
#check CascadeRate.anchorLength
#print axioms CascadeRate.anchorLength
#check CascadeRate.terminalLength
#print axioms CascadeRate.terminalLength
#check CascadeRate.remainderLength
#print axioms CascadeRate.remainderLength
#check CascadeRate.blockCount
#print axioms CascadeRate.blockCount
#check CascadeRate.tailRemainder
#print axioms CascadeRate.tailRemainder
#check CascadeRate.freeCount
#print axioms CascadeRate.freeCount
#check CascadeRate.deficit
#print axioms CascadeRate.deficit
#check CascadeRate.Word
#print axioms CascadeRate.Word
#check CascadeRate.InfiniteWord
#print axioms CascadeRate.InfiniteWord
#check CascadeRate.PrefixClosed
#print axioms CascadeRate.PrefixClosed
#check CascadeRate.Internal
#print axioms CascadeRate.Internal
#check CascadeRate.FiniteContext
#print axioms CascadeRate.FiniteContext
#check CascadeRate.InfiniteContext
#print axioms CascadeRate.InfiniteContext
#check CascadeRate.ShiftClosed
#print axioms CascadeRate.ShiftClosed
#check CascadeRate.SourceContextTree
#print axioms CascadeRate.SourceContextTree
#check CascadeRate.root_internal_of_nontrivial
#print axioms CascadeRate.root_internal_of_nontrivial
#check CascadeRate.internal_prefix
#print axioms CascadeRate.internal_prefix
#check CascadeRate.internal_node
#print axioms CascadeRate.internal_node
#check CascadeRate.nontrivial
#print axioms CascadeRate.nontrivial
#check CascadeRate.exists_context_prefix
#print axioms CascadeRate.exists_context_prefix
#check CascadeRate.cont
#print axioms CascadeRate.cont
#check CascadeRate.cont_spec
#print axioms CascadeRate.cont_spec
#check CascadeRate.context_prefix_unique
#print axioms CascadeRate.context_prefix_unique
#check CascadeRate.lisIndex
#print axioms CascadeRate.lisIndex
#check CascadeRate.lis
#print axioms CascadeRate.lis
#check CascadeRate.alphaLIS
#print axioms CascadeRate.alphaLIS
#check CascadeRate.lisIndex_spec
#print axioms CascadeRate.lisIndex_spec
#check CascadeRate.lis_maximal
#print axioms CascadeRate.lis_maximal
#check CascadeRate.lis_strict
#print axioms CascadeRate.lis_strict
#check CascadeRate.alphaLIS_length
#print axioms CascadeRate.alphaLIS_length
#check CascadeRate.alphaLIS_singleton
#print axioms CascadeRate.alphaLIS_singleton
#check CascadeRate.alphaLIS_preceding_letter
#print axioms CascadeRate.alphaLIS_preceding_letter
#check CascadeRate.alphaLIS_noninternal
#print axioms CascadeRate.alphaLIS_noninternal
#check CascadeRate.Context
#print axioms CascadeRate.Context
#check CascadeRate.contexts_countable
#print axioms CascadeRate.contexts_countable
#check CascadeRate.ProbabilityAssignment
#print axioms CascadeRate.ProbabilityAssignment
#check CascadeRate.fairAssignment
#print axioms CascadeRate.fairAssignment
#check CascadeRate.fairAssignment_law
#print axioms CascadeRate.fairAssignment_law
#check CascadeRate.finiteLaw
#print axioms CascadeRate.finiteLaw
#check CascadeRate.cascade
#print axioms CascadeRate.cascade
#check CascadeRate.cascade_nil
#print axioms CascadeRate.cascade_nil
#check CascadeRate.cascade_factor_valid
#print axioms CascadeRate.cascade_factor_valid
#check CascadeRate.cascade_fair
#print axioms CascadeRate.cascade_fair
#check CascadeRate.cascade_fair_halfpower
#print axioms CascadeRate.cascade_fair_halfpower
#check CascadeRate.kappa
#print axioms CascadeRate.kappa
#check CascadeRate.GeometricDecay
#print axioms CascadeRate.GeometricDecay
#check CascadeRate.ContextAlphaLIS
#print axioms CascadeRate.ContextAlphaLIS
#check CascadeRate.SourceGeometricRateClaim
#print axioms CascadeRate.SourceGeometricRateClaim
#check CascadeRate.alternating
#print axioms CascadeRate.alternating
#check CascadeRate.spine
#print axioms CascadeRate.spine
#check CascadeRate.anchor
#print axioms CascadeRate.anchor
#check CascadeRate.constructionInternal
#print axioms CascadeRate.constructionInternal
#check CascadeRate.constructionNodes
#print axioms CascadeRate.constructionNodes
#check CascadeRate.spine_length
#print axioms CascadeRate.spine_length
#check CascadeRate.anchor_length
#print axioms CascadeRate.anchor_length
#check CascadeRate.spine_prefix
#print axioms CascadeRate.spine_prefix
#check CascadeRate.prefix_spine
#print axioms CascadeRate.prefix_spine
#check CascadeRate.spine_succ
#print axioms CascadeRate.spine_succ
#check CascadeRate.spine_even
#print axioms CascadeRate.spine_even
#check CascadeRate.anchor_literal
#print axioms CascadeRate.anchor_literal
#check CascadeRate.prefix_anchor
#print axioms CascadeRate.prefix_anchor
#check CascadeRate.constructionInternal_prefix
#print axioms CascadeRate.constructionInternal_prefix
#check CascadeRate.constructionNodes_prefix
#print axioms CascadeRate.constructionNodes_prefix
#check CascadeRate.construction_internal_exact
#print axioms CascadeRate.construction_internal_exact
#check CascadeRate.construction_root_internal
#print axioms CascadeRate.construction_root_internal
#check CascadeRate.construction_saturated
#print axioms CascadeRate.construction_saturated
#check CascadeRate.short_shift_subsets
#print axioms CascadeRate.short_shift_subsets
#check CascadeRate.finite_shift_subsets
#print axioms CascadeRate.finite_shift_subsets
#check CascadeRate.spine_two
#print axioms CascadeRate.spine_two
#check CascadeRate.spine_one
#print axioms CascadeRate.spine_one
#check CascadeRate.internal_begins01
#print axioms CascadeRate.internal_begins01
#check CascadeRate.nodes_begins01
#print axioms CascadeRate.nodes_begins01
#check CascadeRate.internal_begins0
#print axioms CascadeRate.internal_begins0
#check CascadeRate.nodes_forbid1child
#print axioms CascadeRate.nodes_forbid1child
#check CascadeRate.construction_no_infinite_shift_subtree
#print axioms CascadeRate.construction_no_infinite_shift_subtree
#check CascadeRate.one_leaf
#print axioms CascadeRate.one_leaf
#check CascadeRate.zerozero_leaf
#print axioms CascadeRate.zerozero_leaf
#check CascadeRate.infinitePrefix
#print axioms CascadeRate.infinitePrefix
#check CascadeRate.infinitePrefix_length
#print axioms CascadeRate.infinitePrefix_length
#check CascadeRate.infinitePrefix_prefix
#print axioms CascadeRate.infinitePrefix_prefix
#check CascadeRate.branch_internal
#print axioms CascadeRate.branch_internal
#check CascadeRate.divergent_bush_bound
#print axioms CascadeRate.divergent_bush_bound
#check CascadeRate.unique_infinite_branch
#print axioms CascadeRate.unique_infinite_branch
#check CascadeRate.alternating_branch
#print axioms CascadeRate.alternating_branch
#check CascadeRate.sourceTree
#print axioms CascadeRate.sourceTree
#check CascadeRate.sourceTree_no_infinite_stable
#print axioms CascadeRate.sourceTree_no_infinite_stable
#check CascadeRate.sourceTree_no_infinite_stable_exists
#print axioms CascadeRate.sourceTree_no_infinite_stable_exists
#check CascadeRate.one_contextAlphaLIS
#print axioms CascadeRate.one_contextAlphaLIS
#check CascadeRate.depth_zero
#print axioms CascadeRate.depth_zero
#check CascadeRate.depth_eq
#print axioms CascadeRate.depth_eq
#check CascadeRate.depth_lower
#print axioms CascadeRate.depth_lower
#check CascadeRate.depth_strictMono
#print axioms CascadeRate.depth_strictMono
#check CascadeRate.index_le_depth
#print axioms CascadeRate.index_le_depth
#check CascadeRate.room
#print axioms CascadeRate.room
#check CascadeRate.decomposition
#print axioms CascadeRate.decomposition
#check CascadeRate.tail_lt
#print axioms CascadeRate.tail_lt
#check CascadeRate.free_le
#print axioms CascadeRate.free_le
#check CascadeRate.deficit_add_free
#print axioms CascadeRate.deficit_add_free
#check CascadeRate.previous_bound
#print axioms CascadeRate.previous_bound
#check CascadeRate.deficit_bound
#print axioms CascadeRate.deficit_bound
#check CascadeRate.deficit_linear_bound
#print axioms CascadeRate.deficit_linear_bound
#check CascadeRate.depth_atTop
#print axioms CascadeRate.depth_atTop
#check CascadeRate.depth_real_atTop
#print axioms CascadeRate.depth_real_atTop
#check CascadeRate.previous_ratio
#print axioms CascadeRate.previous_ratio
#check CascadeRate.deficit_ratio_zero
#print axioms CascadeRate.deficit_ratio_zero
#check CascadeRate.depth_beats_geometric
#print axioms CascadeRate.depth_beats_geometric
#check CascadeRate.abstract_no_eventual_geometric
#print axioms CascadeRate.abstract_no_eventual_geometric
#check CascadeRate.SelectedCode
#print axioms CascadeRate.SelectedCode
#check CascadeRate.selectedBlocks
#print axioms CascadeRate.selectedBlocks
#check CascadeRate.selectedWord
#print axioms CascadeRate.selectedWord
#check CascadeRate.selectedBlocks_length
#print axioms CascadeRate.selectedBlocks_length
#check CascadeRate.selectedWord_length
#print axioms CascadeRate.selectedWord_length
#check CascadeRate.flatten_injective_fixed
#print axioms CascadeRate.flatten_injective_fixed
#check CascadeRate.selectedWord_injective
#print axioms CascadeRate.selectedWord_injective
#check CascadeRate.selectedCode_card
#print axioms CascadeRate.selectedCode_card
#check CascadeRate.anchor_not_prefix_spine
#print axioms CascadeRate.anchor_not_prefix_spine
#check CascadeRate.anchor_prefix_index
#print axioms CascadeRate.anchor_prefix_index
#check CascadeRate.bottom_context
#print axioms CascadeRate.bottom_context
#check CascadeRate.selectedWord_context
#print axioms CascadeRate.selectedWord_context
#check CascadeRate.selectedFamily
#print axioms CascadeRate.selectedFamily
#check CascadeRate.selectedFamily_card
#print axioms CascadeRate.selectedFamily_card
#check CascadeRate.spine_adjacent_ne
#print axioms CascadeRate.spine_adjacent_ne
#check CascadeRate.equal_pair_blocks_spine
#print axioms CascadeRate.equal_pair_blocks_spine
#check CascadeRate.pair_prefix_blocks_spine
#print axioms CascadeRate.pair_prefix_blocks_spine
#check CascadeRate.blocked_tail_no_spine
#print axioms CascadeRate.blocked_tail_no_spine
#check CascadeRate.selectedTail
#print axioms CascadeRate.selectedTail
#check CascadeRate.selectedTail_pair
#print axioms CascadeRate.selectedTail_pair
#check CascadeRate.selectedTail_no_spine
#print axioms CascadeRate.selectedTail_no_spine
#check CascadeRate.selectedWord_shift_no_spine
#print axioms CascadeRate.selectedWord_shift_no_spine
#check CascadeRate.selectedWord_short_suffix
#print axioms CascadeRate.selectedWord_short_suffix
#check CascadeRate.selectedWord_suffix_not_spine
#print axioms CascadeRate.selectedWord_suffix_not_spine
#check CascadeRate.selectedWord_suffix_noninternal
#print axioms CascadeRate.selectedWord_suffix_noninternal
#check CascadeRate.selectedWord_lisIndex
#print axioms CascadeRate.selectedWord_lisIndex
#check CascadeRate.selectedWord_lis
#print axioms CascadeRate.selectedWord_lis
#check CascadeRate.selectedWord_alphaLIS
#print axioms CascadeRate.selectedWord_alphaLIS
#check CascadeRate.sum_fin_cast
#print axioms CascadeRate.sum_fin_cast
#check CascadeRate.selectedFunction
#print axioms CascadeRate.selectedFunction
#check CascadeRate.selectedFunction_word
#print axioms CascadeRate.selectedFunction_word
#check CascadeRate.selectedFunction_injective
#print axioms CascadeRate.selectedFunction_injective
#check CascadeRate.selectedWord_weight
#print axioms CascadeRate.selectedWord_weight
#check CascadeRate.selected_kappa_lower
#print axioms CascadeRate.selected_kappa_lower
#check CascadeRate.fixed_kappa_not_geometric
#print axioms CascadeRate.fixed_kappa_not_geometric
#check CascadeRate.source_geometric_rate_refuted
#print axioms CascadeRate.source_geometric_rate_refuted
#check CascadeRate.SourceContextTree.nodes
#print axioms CascadeRate.SourceContextTree.nodes
#check CascadeRate.SourceContextTree.prefix_closed
#print axioms CascadeRate.SourceContextTree.prefix_closed
#check CascadeRate.SourceContextTree.root_internal
#print axioms CascadeRate.SourceContextTree.root_internal
#check CascadeRate.SourceContextTree.saturated
#print axioms CascadeRate.SourceContextTree.saturated
#check CascadeRate.SourceContextTree.countable_branches
#print axioms CascadeRate.SourceContextTree.countable_branches
#check CascadeRate.ProbabilityAssignment.law
#print axioms CascadeRate.ProbabilityAssignment.law
#check CascadeRate.ProbabilityAssignment.positive
#print axioms CascadeRate.ProbabilityAssignment.positive
#check CascadeRate.ProbabilityAssignment.normalized
#print axioms CascadeRate.ProbabilityAssignment.normalized
