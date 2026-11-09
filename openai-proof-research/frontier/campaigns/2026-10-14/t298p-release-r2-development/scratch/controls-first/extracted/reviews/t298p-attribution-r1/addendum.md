# T298P attribution and comparison addendum

This is parent author-side work on the unchanged sealed candidate in `fresh-structural-discovery-r104`. It responds to the four attribution requirements in the unsealed contribution-round-1 draft. That task failed on a provider rate limit before sealing. Its proposed SUBSTANTIAL classification is not an adopted gate. Fresh independent contribution round2 and proof round1 are separate tasks. This addendum changes no theorem, proof estimate, frozen byte, scope, or count.

## Location of the proposed contribution

The scalar matrix pair, its tangent/normal dimensions, local slice inversion, group-volume formula, orbit-volume constant, lower-volume packing pattern, coefficient normalization, and orthogonal semicircular rotation are credited classical tools. They are not claimed as new results.

The proposed new bridge consists of the following coupled deductions, subject to independent proof and contribution review:

1. The unconditional Fisher bound for the encoded pair, with leading term `Phi*(U)/(epsilon^2 k^4)` and an orbit-direction remainder whose heat integral is `O(epsilon)`. The coefficient-space construction combines normal entry derivatives and inner derivatives; it must establish legitimate adjoints without discarding matrix-unit conditioning.
2. The unconditional upper microstates-volume bound at every output size, using the pair's own spectral bands and tree-polar coordinates to recover matrix units, a common-root truncation, source-law reconstruction, and vanishing-rank volume accounting. It retains the original cutoff/ordinary-limsup entropy and the same orbit constant as the lower bound.
3. Coupling these two estimates along the exact noisy encoding so their common constants cancel and the finite source gap survives in a pair.

Calling the entire normal-bundle geometry new would overstate this claim. Global tube injectivity is supporting geometry. The all-size, intrinsic upper recovery and the unconditional cheap-orbit score estimate are the specific operations for assessment. No worldwide priority claim follows from this comparison.

## R1: orbit geometry and its constant

Nica, Shlyakhtenko and Speicher, *Maximality of the microstates free entropy for R-diagonal elements*, [math/9809081v1](https://arxiv.org/abs/math/9809081v1), already use an orbit/slice measure factorization. Lemma2.6 computes the polar-coordinate measure factor. Lemma2.8 states the normalized unitary-volume limit `3/4 + (1/2)log(2pi)` in their `Re Tr(ab*)` metric. Lemmas2.9 and2.10 use the resulting upper-volume and lower-packing operations, with the latter under a free Haar/positive-variable hypothesis. The unitary-group volume formula and the resulting constant are paid antecedents.

The candidate's `c` is exactly this classical constant in the same unnormalized Hilbert-Schmidt metric. Its quotient stabilizer scaling, repeated tangent singular values, and cancellation of logarithmic normalization factors are finite-dimensional bookkeeping. The cited polar/R-diagonal theorem does not, under its actual hypotheses, supply an arbitrary-source normal-tube upper recovery theorem. The candidate must establish that latter operation separately; this is not inferred from a difference in terminology.

## R2: supplied matrix units and corner compression

Shlyakhtenko, *A Microstates Approach to Relative Free Entropy*, [math/9812079v1](https://arxiv.org/abs/math/9812079v1), Section5 and Theorem5.1 already supply matrix-entry compression and measure-preserving packing relative to a scalar matrix algebra. Its proof chooses a corner under a supplied model of `E_11`, compresses by the supplied matrix-unit models, and controls the resulting entry microstates. This pattern is credited.

The Section5 equality is formulated for ultrafilter entropies, with its explicitly dilated ultrafilter. Its displayed ordinary-limsup conclusion is one-sided. Neither is silently converted into an unconditional equality for the candidate pair. In particular, the candidate's matrix units must be recovered from arbitrary pair microstates, and the ordinary-limsup upper bound must cover all output sizes, including sizes not divisible by `k`. These are stated obligations of the new argument, not consequences attributed to Section5.

## R3: standard entropy inputs and their scope

The Gaussian smoothing lower bound is Shlyakhtenko Proposition4.2: for an embeddable bounded tuple and a free variance-one semicircular family, `chi(X+sqrt(t)S) >= (n/2)log(2pi e t)`. The displayed proposition in arXiv v1 prints `n` where its proof gives `n/2`; the candidate uses the latter normalization, consistent with its own semicircular convention. The embeddability hypothesis is retained. This is a credited input, not a new smoothing estimate.

The relative-to-unconditional microstates inequality follows from that paper's Proposition2.8 together with the ordinary projection inequality `chi(H:T) <= chi(H)`. The relative entropy here is its supremum-over-models definition, not a joint-minus-conditioning expression. Theorem2.19 pays free conditioning, and Theorem4.1 pays change of variables by inverse noncommutative power series with the printed common-multiradius and strict norm hypotheses. The proof of Theorem4.1 is omitted in v1 by reference to Voiculescu's change-of-variables argument. We use its stated classical theorem and explicitly expose that dependency; this note does not claim to have read a proof absent from that version. The candidate must supply the convergent inverse and verify those hypotheses.

The covariance upper bound for nonmicrostates entropy belongs to Voiculescu's Fisher-information/free-entropy theory. Its scalar-trace form can also be read directly from the stipulated normalization. Put `c = sum_i Var(X_i)/n > 0`. The conjugate identities and Cauchy-Schwarz give `Phi*(X+sqrt(s)S) >= n/(c+s)`. Integrating this lower Fisher bound in the defining entropy integral gives `chi*(X) <= (n/2)log(2pi e c)`. This elementary derivation is classical and earns no contribution credit. The pertinent reference is D. Voiculescu, *The analogues of entropy and of Fisher's information measure in free probability theory. V. Noncommutative Hilbert transforms*, Invent. Math.132 (1998),189-227, [doi:10.1007/s002220050222](https://doi.org/10.1007/s002220050222).

The comparison `chi <= chi*` is credited to P. Biane, M. Capitaine and A. Guionnet, *Large deviation bounds for matrix Brownian motion*, Invent. Math.152 (2003),433-459, [doi:10.1007/s00222-002-0281-4](https://doi.org/10.1007/s00222-002-0281-4), and D. Jekel and J. Pi, *An elementary proof of the inequality chi <= chi* for conditional free entropy*, Doc. Math.29 (2024),1085-1124, [doi:10.4171/DM/969](https://doi.org/10.4171/DM/969). The parent checked these citations in the actual pinned source298 introduction and bibliography; it has not newly read those whole external papers for this addendum.

Source298 `02-conventions.tex`, equation `eq:chistar`, fixes the integral normalization. Its `04-signal.tex`, equation `eq:freeflow`, gives the finite heat increment for its smoothed source. The general heat identity along the encoded pair is the same classical free heat-flow identity, invoked only once finiteness and the candidate Fisher bound have been established. No new entropy-comparison or heat-flow theorem is claimed.

## R4: the pinned two-generator result

The pinned preprint *Relative generation and the generator problem for finite factors* (September23,2026), introduction Theorem `thm:main`, proves two-self-adjoint generation for every separable-predual II1 factor. Its consequences section, Corollary `cor:entropy-generators`, explicitly shows that the microstates entropy dimensions can depend on the chosen generating tuple. These actual statements and their companion comparison have been read; their construction proofs have not been re-audited, in accordance with the stipulated-source contract.

That theorem pays generation of an algebra. It gives no entropy-value or finite-gap invariance when replacing a tuple by generators. Source287's coordinatewise isomorphism transport preserves length and joint law; it also does not provide the two-coordinate gap. T298P does not assert that the encoded pair generates its entire ambient algebra. Combining a many-variable gap with a two-generator theorem alone is therefore not the candidate's argument. The new generator-source receipts in this packet authenticate the three actually read canonical files against the complete pinned tree.

## Quantitative limitation of the paid relative route

This comparison does not prove the proposed unconditional estimate. It explains why the paid relative estimate alone is insufficient for this encoding. At positive source-noise time `u`, the normal and orbital coefficient tuples are `(U(u), sqrt(u)R)`, where the orbital tuple has `k^2-1` semicircular coordinates. NSS *Some minimization problems for the free analogue of the Fisher information*, [math/9809080v1](https://arxiv.org/abs/math/9809080v1), Proposition4.1, with projection gives a relative upper bound containing

    [Phi*(U(u)) + (k^2-1)/u] / (epsilon^2 k^4).

With `dt = epsilon^2 k^2 du`, its extra contribution between `u0` and `U` is `((k^2-1)/(2k^2))log(U/u0)`, which diverges as `u0` decreases to zero. At zero orbital noise the coefficient tuple lies in a lower-dimensional affine space and has negative-infinite entry microstates entropy, so a relative lower-volume bound alone does not repair this loss. These are limitations of those operations, not impossibility claims for other paid theorems or a proof of novelty. The separate contribution review decides whether a closer result supplies the candidate's proposed bridge.

The existential bound has factor `k^-2`, with `k=2^32`. There is no effective useful epsilon or numerical pair witness. No widened general transfer theorem is added to the frozen target in response to an optional editorial suggestion.
