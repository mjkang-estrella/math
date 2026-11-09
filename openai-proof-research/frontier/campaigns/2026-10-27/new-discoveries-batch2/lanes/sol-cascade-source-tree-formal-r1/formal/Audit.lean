import TreeConstruction
set_option autoImplicit false
set_option warningAsError true
set_option pp.universes true
set_option pp.fullNames true
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
