# H040 information lens: retain missing operators, reject blanket gates

2026-10-08. Factory Claude Opus5.5 raw report retained separately. It submitted
no new candidate and reported no fresh full primary-source reads. Root reopened
the primary bounds below and assigned distinct native reviews: Sol on sampling,
cost and scope; Astra on correspondence geometry and interval membership.
Both native reviews completed and confirmed the corrected scopes below.
No experiment, new Lean claim or baseline change. Review completion and exact
handles are recorded in STATE.md.

## Passive phase harvesting is conditional

Let F(n)=f([n]G), |F|<=1, and c_a=q^-1 sum_n F(n)e(-an/q). For an independent
uniform shift d, substitution proves

    E_d F(k+d)e(-ad/q) = e(ak/q)c_a.

Thus an estimator needs the complex coefficient c_a, not just its magnitude.
Calibration, precision, confidence, zero/small coefficients and phase ambiguity
must be paid. State-dependent walk offsets need not be uniform or independent;
knowing their scalar labels does not supply the asserted sampling variance.
Even marginal uniformity is insufficient for a 1/N variance bound without
controlling covariance. Frequency selection and validation cannot be free.

If a particular sampler justifies O(N^-1/2) error, calibration is comparably
accurate, and a known nonzero coefficient has magnitude epsilon, then the
claimed residual width q/(epsilon sqrt(N)) is a CONDITIONAL phase-to-interval
estimate (truncated to the valid range). A nonzero frequency can be handled by
the corresponding known scalar transformation; this too must be charged.
Ignoring confidence factors and all ancillary costs, minimizing

    N + A N^(-1/4), A=sqrt(q/epsilon)

gives N=(A/4)^(4/5) and work Theta((q/epsilon)^(2/5)). If epsilon=q^-b this
model beats square-root growth only for b<1/4. It is a gate for THIS model,
not a universal sample lower bound or classification of every ECDLP decoder.
In particular, no full-work solver follows without the missing named feature,
calibrated sampler and success/failure accounting. At confidence1-delta, the
phase-radius estimate also carries sqrt(log(1/delta)); a useful sub-turn radius
requires epsilon*sqrt(N) much larger than this factor. Calibration must resolve
that same shrinking phase scale, not merely estimate c_a to constant relative
accuracy. If failure probability delta invokes a fresh Theta(sqrt(q)) baseline,
constant delta retains a square-root expected term. A successful q^alpha
pipeline with alpha<1/2 needs delta=O(q^(alpha-1/2)) up to logs, or a justified
independent retry policy with uniform success and paid attempts. IID confidence
amplification can achieve polynomially small delta with logarithmic overhead;
an unproved correlated-walk model does not supply that amplification.

Multiplication-orbit sampling can update a character value cheaply once its
phase is known, but a short orbit of2 or3 may sample a proper subgroup or have
poor correlation control. Character conversion, point multiplication, starts,
calibration and confidence remain paid; it is not automatically equivalent to
H013's independently randomized progression blocks. An approximate
multiplicative-character phase selects cosets or a union of cosets, not an
additive scalar interval. The passive kangaroo invoice cannot automatically
transfer to that setting; H013 separately charges fine m-root phase separation
and its explicit multiplicative-coset search.

## Character-bound scopes

Root freshly read [Kohel–Shparlinski, Section3, Theorem1/Corollary1](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf).
In project notation its mixed group/additive-field-character bound is at most
2d sqrt(p), before normalization by subgroup order q. Retain H026's
nondegeneracy/pole qualifications: expressions of Artin–Schreier form can give
constant characters. Fourier expansion of an applicable observable contributes
its actual L1 norm. The result is an upper bound, not an attained correlation.
Having d*L sufficiently large merely makes a bound inconclusive; it constructs
no useful signal and is not a universal necessity for arbitrary cheap features.

Root freshly read [Ahmadi–Shparlinski, Lemma2](https://arxiv.org/pdf/1302.4210).
H013's application to a multiplicative scalar character and an additive phase
of x on an ordinary curve gives normalized O(q^-1/12 log^(1/3)q) when q is
comparable to p. This is NOT a ceiling for every public feature or arbitrary
Legendre product. Observable extensions pay Fourier norms or need new pole/
character arguments. A weak upper bound larger than a hoped-for signal is
neither positive evidence nor a construction. The raw generalization is rejected.

## Membership is not oriented interval membership

For J subset of scalar indices with finite affine points, the root test

    product_(j in J)(x(Q-[a]G)-x([j]G)) = 0

accepts k-a in J union(-J) modulo q. It does not test only k in a+J.
For q=7, a=0, J={1,2,3}, Q=[6]G=-G produces a hit at j=1 despite k=6
being outside the intended lower half. Treat j=0/infinity by a separate sentinel;
that does not repair the false positive. Discarding the other half on this hit
can discard the correct scalar. The raw statement that bisection is already a
valid index-recovery procedure is therefore withdrawn. A repaired search would
need sign/orientation and coverage/recovery invariants with paid work.
Neither a big-O polylog upper bound nor a geometric sum of such upper bounds
alone proves loss against a complete baseline. No universal lower bound on
compressed membership methods follows from this counterexample.

## Correspondence qualifications

Astra checked the generic genus calculation: over an algebraic closure, two
quadratic cubic covers with disjoint sets of three finite roots share infinity.
If their square classes are independent, the normalized connected V4 cover has
seven inertia-two branch places. Riemann–Hurwitz gives
2g-2=-8+14=6, hence g=4. At zero shift for a quadratic twist the square classes
coincide geometrically; the fiber product instead splits into elliptic
components after a constant extension. Other branch intersections also require
separate normalization/ramification accounting.

A chosen coordinate branch is not automatically a full rational-point sum on
that normalization. A 6sqrt(p) character bound additionally requires the actual
nontrivial geometric character, conductor and summation domain; none was
established for the proposed chosen-branch observable. The complete pair of
opposite points sums to zero, but that fact does not turn an arbitrary selected
branch into a group homomorphism. No universal branch-transfer exclusion is
accepted. This is a missing construction/hypothesis finding.

## Decision

No feature or decoder is promoted. The proposed future FFT sweep is not admitted:
floating-point FFT is not exact without error certification, and enumerating
every group point/feature, character indexing, transformed samples and selection
over many features must all be paid. A random-noise maximum is a conditional
comparison model, not a theorem about deterministic curve features. Small-curve
results cannot alone establish asymptotic rejection or a full-size gain.

Best supported exponent1/2; verified improvement NONE. Grok's independent H040
geometry proposal remains pending. The next useful evidence is an explicit
scalar-sensitive feature/operator with a scoped success mechanism and full-cost
prediction, not a larger decoder stack or an unspecified feature search.

Validation: ./scripts/check.sh > /tmp/ecdlp-h040-information-check.log 2>&1
exit0 (366 existing audits); no new Lean/Audit declarations. Primary sources
were opened through web at the cited theorem passages; no numerical run.
