# Statement correspondence

This is an implementation continuation, with zero acceptance credit. The geometry, percolation definitions, counterexample bridge, finite-system encoding and projective normalization are inherited byte-identically from the round 6 archive. See retained-source-comparison.json for hashes. No primary-source or novelty investigation is claimed in this lane.

The target remains `Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20`, through `Percolation.NoMinimalTwoRound5` and `Percolation.GeneratedNormalizedUnsat5`. A partial endpoint is explicitly conditional and does not assert either target without its premise.

The numeric DIMACS convention maps literal x to `(abs(x)-1, x<0)`. A literal `(n,b)` holds when the valuation at n differs from b. `decodeVar` maps the numeric index to the inherited structured variable. The new mask entailments quantify over structured valuations `v : SatVar → Bool`, assume every clause of `normalizedCNF5`, and conclude `MaskRUP.Holds (v ∘ decodeVar) mask`.

For an input, a literal-list theorem is proved from the inherited generator gate, nonfull, omit, contain or normalized-unit lemmas. A kernel-checked equality `MaskRUP.encode inputClause = numericMask` transports this theorem using the proved encoding equivalence. The data-preparation script is not a proof oracle.

For an addition, the builder constructs a reflexivity proof of the concrete mask check and supplies every hint's named entailment theorem to `MaskRUP.check_sound`. There is no free hint assumption. Both Lean's declaration kernel and the explicit-module leanchecker validate these terms. Certificate deletion commands need not be replayed: retaining an already proved consequence is sound.

The remaining-suffix condition is a precise satisfiability statement for the normalized generator together with the last closed prefix clause. It is implied by a replay of the actual remaining certificate suffix ending with the empty clause, but that implication is not asserted as completed until those steps are checked.
