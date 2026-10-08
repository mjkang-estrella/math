# H022 lazy-prefix EDS: support cost remains unfavorable

2026-10-08. Native Sol proposer and NEW Claude Opus independent review
COMPLETED; terminal result read/no pending children. Raw retained in
H022-lazy-EDS-opus-raw.md; exact task/brief in H022-lazy-EDS-review.md.
Root checked the recurrence dependencies and arithmetic below. Paper finding,
not Lean proof or experiment. Verified improvement NONE.

## Accepted literal schedule and costs

Use the proposed common phi(G) normalization, with UNSCALED DG support for
the scaled dynamic target terms. This is homogeneity of the dynamic recurrence
with its support fixed; it is NOT invariance of the entire Ward sequence
under arbitrary constant scaling.

Known keys use the primary Eq15/16: even output3M, odd output2M, using
precomputed h2 inverse. Need C,D through about half the known prefix, adding
.5(M+S) per key. Bootstrap h0 through h5 so that producing D_(l+1) never
requires an unavailable h_(l+2). Leading known cost is cg=3+.5s, s=S/M.

For targets t_j=phi(Q-jDG)/phi(G), bootstrap j=-1,0,1,2. The pair j=2l,
2l+1 uses parents j=l-1,l,l+1. Starting at l=2 makes all parents already
available. The l=1 pair is circular and must not be used for bootstrap.
Anchors t0 and t_-1 are inverted once. Shared dynamic numerator work and
two outputs cost7M+S per pair. The separate public DG support through
J/2+O(1) costs3.5M+S per support index, including generation of those known
terms and their C,D values. Its inner half-prefix support is part of this
same retained table, not an additional free sequence or a second charge.
Leading target cost is cb=5.25+s.

Zero anchors correspond to Q=O or Q=-DG and yield directly verifiable
scalars. Other zero target keys likewise identify their offsets; known zero
is only a sentinel. Keep indexed support/parents as proposed, with O(sqrt(q))
records. Bootstrap, point-function evaluation, stride construction, all fixed
inversions, field additions, access, key traffic and verification remain paid.

## Coverage and arithmetic screen

Signed POINT matches yield k=jD±i. Raw EDS equality alone need not be a point
match; check candidates and retain all equal-key indices. Correct prefix caps
I≈D/2,J≈q/D cover the full range with rounding/endpoints. Under uniform k,
the true point coverage along prefixes is2IJ up to boundary terms. Balance
paid prefix growth cg*I=cb*J and choose D²≈2cb*q/cg. In the leading model,
covered fraction at paid cost w is w²/(2cg*cb*q) until full coverage.
Integrating its complementary probability gives expected arithmetic

    (2sqrt2/3)*sqrt(cg*cb*q).

This is optimal among these rectangular-prefix paths with the stated linear
costs; it is not optimal among all algorithms. Finite rounding/granularity,
setup and exceptional events require their own charges. Compare H019's
matched limiting x-only coefficient (2sqrt2/3)*(2.5+s). Since

    cg*cb-(2.5+s)² = 9.5+.625s-.5s² > 0,  0<=s<=1,

the specified computation has no leading arithmetic gain, even before its
false-match work. These are the specified recurrence operation counts, not
a lower bound on every way to evaluate EDS terms. No finite hardware/runtime
claim or multi-target amortization result follows.

## Corrections to the independent review

Its assertion that raw phi equality implies equal or opposite points is
false without injectivity, and its displayed comparison also omits the common
normalizing denominator. Coverage above counts true point relations only.
Extra key matches cannot be discarded silently or assumed O(1). The literal
SCM-per-match verifier is one option, not a necessary lower bound: a new H023
neighbor-based exact filter is being developed separately, not yet accepted.

Do not accept O(1) total support storage for this retained-table ledger.
For the public DG stream, C_m,D_m may be used by target output near2m and
again by generation of public g_(2m) near target output4m. Discarding them
after the first use requires charged recomputation or a different schedule.
Keeping the proposed arrays preserves the reviewed operation count and
O(sqrt(q)) storage bound; no extra storage optimality claim is needed.

The review's additional multi-anchor/parity/idealized-floor variants are
unreviewed leads, not necessary lower bounds or accepted new algorithms.
Its 'reasonable batch size' claim is not a quantified finite comparison.
Point-function bootstrap remains paid with the source's model distinguished
from field-operation counts; we do not upgrade it to a measured runtime.

Decision: reject this literal lazy-prefix gain rationale, while retaining
the explicit schedule. No prototype justified. A different paid support
schedule or materially different complete-cost regime can reopen it; no
universal EDS failure is claimed. The ordinary square-root reference remains.
