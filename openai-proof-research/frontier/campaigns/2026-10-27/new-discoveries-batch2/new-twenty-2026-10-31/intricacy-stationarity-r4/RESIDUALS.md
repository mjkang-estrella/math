# Exact endpoint unresolved — zero credit

## Closed since r3

The exact translated cylinder target is `MathDB333569.twoSidedLaw_word` in Stationarity333569.lean. This is an equality about r3's actual countably additive law, with no stationarity/consistency assumption. `twoSidedLaw_shift` closes actual integer-shift invariance. `twoSidedLaw_marginal`, `twoSidedLaw_prefix_next`, and the finite rank-zero entropy identities close the finite-law/source-definition identifications. `rankZero_blockEntropy_chart` gives actual block entropy in source coordinates. Full support remains the inherited proved instance.

## Precise next bridge

Prove, for any strictly increasing `s : Fin (d+1) → ℤ` and assignment `a`,

`twoSidedLaw (chart l t) hz {x | ∀ j, x (s j) = a j} =
 ENNReal.ofReal (pi t (a 0) * ∏ j : Fin d,
   kernel (l ^ (s j.succ - s j.castSucc).toNat) t (a j.castSucc) (a j.succ))`.

Hypotheses are `0<l<1`, `-1<t<1` and strict increase of s. The exponent is a positive integer gap. No conditional-independence hypothesis may replace this proof. The actual selected marginal is already identified with the finite source marginal; its sparse sum must now be contracted into powers using `steps_eq`/`kernel_comp`. The finite Shannon chain rule is available in FiniteEntropy333569, but it does not itself prove this contraction. After contraction, prove selected entropy equals H(pi) plus the sum of conditionalEntropy at consecutive gap powers, including empty and singleton samples.

The next combinatorial identity, writing N=n+1, is

`2 * (sum_S sampleEntropy z n S) / 2^N =
 2*(1-2^(-N))*H(pi) + sum_{1<=i<N} (N-i)*2^(-i)*H(l^i,t)`.

Then divide by N, subtract the now-proved block entropy/N, prove convergence, and identify the limit of the actual rank-zero finite intricacy with `sum_{i>=1} 2^-i H(l^i,t)-H(l,t)` for all nearby parameters. Uniform weights and natural logarithms must be preserved.

## Untouched major endpoint obligations

1. Identify H_tt(r,0)/2 with transverseCoeff. Prove uniform first/second transverse derivative bounds, summed derivative identities and joint continuity. Neither the diagonal maximum nor the coefficient-series sign proves this.
2. Promote negative transverse curvature and the existing diagonal maximizer to a two-dimensional local maximum of the actual entropy-series functional, and transfer through the proved limit identification.
3. Define and cover ALL stationary one-step Markov laws in a relative weak neighborhood, including boundary/nonergodic laws unless proved open neighborhood conditions exclude them. Prove cylinder-ratio recovery, chart continuity and local topology equivalence. Finite-cylinder factorization here is not a bundled conditional-expectation Markov API theorem or this all-law coverage theorem.
4. State/prove the literal final measure theorem, obtain independent formal/source-fidelity review, write the paper and undergo root acceptance. The finite-parameter SourceClaim is still unproved and would not alone be the literal source theorem.

## Approaches and failures

The r3 measure construction was reused, not reproved. A literal rectangular pullback of a mixed window fails at coordinate zero: glue uses the forward trajectory there. The successful correction proves both trajectories start at the mixing symbol almost everywhere, then uses product almost-everywhere equality and measure_congr. Weighted path reversal avoids dividing by stationary probabilities. Chronological product flattening uses Fin.revPerm and Fin.prod_univ_add; left and right finite disjoint marginalization extend crossing-zero windows to every translated interval. Cylinder uniqueness factors any finite coordinate restriction through a containing block; no stationarity assumption is smuggled into uniqueness.

The general sparse product is not a consequence of `marginal_restrict` alone: that theorem retains a sum over unselected symbols. The contraction of that sum, with arbitrary ordered gaps, remains unclosed. No failed library search is claimed to prove impossibility, and no mathematical counterexample or lack-of-library obstruction is asserted. This is incomplete proof development with the next algebraic/semantic bridge precisely identified, not a completed endpoint.
