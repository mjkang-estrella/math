# H022 — Coordinator disposition

2026-10-08. **ACCEPT Sections 1–4 after independent review; ACCEPT the repaired
Section 5 after coordinator checking of its explicit sufficient model.**
Verified full factoring complexity improvement: **NONE**.

## Evidence

The [independent review](H022-independent-review.md) accepted the generalized
finite count, fixed-parameter population envelope, actual-height accounting
and exact optimization of the displayed conditional relaxation. It required
precise uniformity, expected-work, adaptive-yield and norm-mesh assumptions
for the mixing extension.

The 289-line [submitted draft](H022-submitted-draft.md) is preserved byte-for-byte,
SHA256 `ecae556871c90be3eb31bc0b7bcba49d58e201079d4603a86e71cc1dfa09754f`.
Review SHA256:
`dfcd1e6e11c3928058c2a3517babf8a03a073abc0ec58049ce84e252365b52bb`.
The coordinator read the full review and verified all 17 completion input
hashes plus both owned-output hashes in its provenance manifest. STATE's
capture-to-completion change was legitimate shared checkpoint work and did
not change mathematical dependencies. These hashes establish provenance only.

## Required repair and its check

The [corrected report](H022-stratified-linear-envelope.md) now states a
predetermined disjoint reference partition, one fixed f/degree sequence,
fixed positive delta,b, a compact positive range for height parameters,
bounded thresholds and uniform asymptotics/geometry. A moving winning bin
cannot be justified by pointwise limits. F is retained as an upper envelope,
not a pointwise sharp count or an attained supply law.

For attempts M_j, useful outputs Y_j and total work C_N, require pathwise
M_j<=S_j and sum M_j<=C_N, plus the aggregate law
E Y_j<=p_j E M_j for the actual strategy. The review-supplied history-wise
conditional law is sufficient by the tower property and monotone summation
of nonnegative contributions, including stopping. It is not derived from
an unconditioned average smoothness rate. Post-selected partitions require
their own justified reduction or conditional law.

Population uses the upper norm endpoint and yield the lower one. The report
keeps their gap Delta. The coordinator checked every step of the repair:
expected-output pigeonhole; positive attempt exponent from b>0; compact
subsequence for size-dependent bin parameters; continuity across the F
branches; and the following exact limiting chain, A0=1+gamma:

    u<=aF, b<u<=c,
    W^+<=3u²/4+Delta,
    (W^+)²=a(z+K)²/z>=u(z+K)²/(zF)>=2A0u.

All divisors and squared quantities are positive. Expanding the square and
dividing by 9u/16 gives

    32A0/9 <= u³+(8/3)u Delta+(16/9)Delta²/u
            <= c³+(8/3)c Delta+(16/9)Delta²/b.

Thus a uniformly vanishing mesh gives c³>=32(1+gamma)/9.
Arbitrarily fine fixed meshes also suffice in the stated ordered limit if
the same strategy and yield hypotheses survive subdivision. One positive
mesh alone proves only the perturbed inequality. No independence or optional
stopping assertion is hidden. The total exceptional population J_N d has
zero exponent relative to D and cannot meet the fixed positive-b target.

This is coordinator checking of the new review-supplied repair, not a second
T3 review round or a Lean proof. No additional geometry or distribution lemma
is inferred.

## Accepted result and limits

The infimum of the displayed real inequality relaxation is

    c_*³=32(1+gamma)/9, 0<=gamma<=1,

with the equality parameters verified in the independent review. The compact
mixed model has the same infimum only when its allowed degree/parameter ranges
include that witness. For one prescribed f/degree sequence, only the lower
bound is asserted; no actual candidate population or useful yield is attained
by assigning the equality parameters.

gamma=1 recovers the conventional single-polynomial GNFS model constant;
gamma<1 retains the smaller-coefficient advantage, including gamma=0's SNFS
constant. Multipolynomial sharing, changed samplers, vanishing b, unbounded
height or uncontrolled degree sequences are outside the repaired statement.
This is no factoring lower bound. No actual geometry frequency, smoothness
law, rank, algebraic square root or proper-split guarantee has been proved.

For rational threshold Q=p/q the finite cleared-power identity is accepted;
a separate bit-cost implementation must bound magnitudes p,q and integer
widths. Binary encoding alone cannot make arbitrary qd-th powers cheap.

## Next decisive branch

H023 asks whether an explicitly recognizable ordinary-base family has strongly
clustered roots and a useful costed anisotropic relation space. Its proposed
geometry escape and heuristic optimization remain unreviewed. Construction
cost, irreducibility, special-family prior art and full relation processing
are part of that task. Retuning bins within H022's accepted assumptions is
closed by this conditional model result, not by an unconditional hardness claim.

No executable, numerical experiment or Lean change was made for H022 or this
repair. The prior shared checks were not repeated for these document changes.
