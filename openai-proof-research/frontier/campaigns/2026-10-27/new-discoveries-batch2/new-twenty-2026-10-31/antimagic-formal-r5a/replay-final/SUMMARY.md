# Round 5A construction handoff

PARTIAL, NOT ACCEPTED. No credit claimed; root decides.

For every even t >= 4 and n >= 3, this round constructs the complete literal
edge equivalence higherLabeling and proves exact agreement with the frozen
formula, with positive labels covering the full edge interval. The internal
shell row intervals, internal-vertex permutation, parent-derived leaf tuple
parameter permutation and leaf-row permutation are now proved symbolically.
The middle children sums and constant last-parent sums are also proved, and Antimagic5AWeights transports them to literal incidence weights.

NonbinaryHigherConstruction is still conditional: properness, the global
weight/colour ranges, root separation and exactly t^n+1 colours remain open.
The precise residual definition is NonbinaryWeightCompletion. The final
nonbinaryHigherConstruction_of_weights theorem reduces the inherited Prop to
this smaller obligation. The final even_case assumes this residual and
BinaryHigherConstruction; mathdb_354228 additionally assumes ModelBridge.
Neither complete higher-depth construction family is claimed closed.

The binary higher construction has not been started, preserving the target
order. ModelBridge was not worked on. All 27 inherited modules are byte-identical
to source.zip SHA256 2ecbbae0f5804c5d9c5d3a2b83b2789a7c359edc7162f2c3dbfc42f58cef8516.

See results.json and replay-final for extracted strict serial rebuild,
explicit leanchecker checks, full declaration audit and numerical regressions.
Only propext, Classical.choice and Quot.sound are allowed. REPRODUCE.md gives
the resumable driver, fixed dependencies and resource caps. PROOF.md explains
all new symbolic steps and their limits.

Next round: using the proved literal weights for
higherLabeling, prove Z <= q, tZ >= N, the root formula and root separation;
place all non-exceptional weights in the leaf band and the last-parent constant
above every label; use injectivity for adjacent middle rows and lowerBound for
the exact colour count. Close NonbinaryWeightCompletion before starting the
binary patch. Leave ModelBridge to the sibling lane.
