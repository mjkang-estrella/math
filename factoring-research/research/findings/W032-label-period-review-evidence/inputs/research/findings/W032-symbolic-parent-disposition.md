# W032 symbolic construction and affine lift: parent disposition

Accept the scoped results of both reviews, with the qualifications below.
Verified complete factoring improvement: **NONE**. The scalar/carry report
(555 lines), its symbolic source and all 11 check outputs, and the lift
report (194 lines) were read in full. All 17 scalar and 15 lift payloads
match their delivery manifests, including both external terminal anchors;
see `W032-symbolic-parent-intake.json`. No parent numerical rerun occurred.

The accepted scalar diagonal satisfies the lift review's provisional import.
Exact N^2 division, working precision N^(2R+3), omitted-tail argument without
false distant N-divisibility, and canonical precision consistency all pass.
The first digit is a unit; d2 has the stated quartic formula and the upper
zero count 96 ceil(q/24) for N=pq. Unit conditioning divides by phi(N), not
N. Proper splitting requires exactly one vanishing component for squarefree
semiprimes. The common-denominator floor formula passes for negative and
noncanonical integer lifts as well.

The exact third digit now has a smaller direct description. Put

    r=(-a^2 mod24), P=9a^4-80a^2-80r,
    s=(-P*(N^2)^(-1) mod1920),
    ell=floor((P+sN^2)/(1920N^2)).

For canonical unit a and leastprime(N)>7,

    d3=5a^6/7168-a^4/192-s/1920+ell modN.

The integer ell varies within small residue classes. A degree-six bound
applies after fixing its label, not to the entire canonical input set.
The review supplies a symbolic family demonstrating this variation. Its
11 exact rational-polynomial checks do not certify the floor inequalities,
general-R argument or success law; those remain prose mathematics.

Acquisition is soft O((R+1)*bitlen(N)^2) under the specified fast-arithmetic
model. All R digits need a paid radix conversion plus R gcds. Literal repeated
large division has its own cost; do not silently assign it the fast conversion
bound. For fixed R a small floor-polynomial screen computes the same data
without binary powering. For growing R the direct coefficient method has
O(R^2) coefficient work and O(R) wide per-point Horner steps, so it is not
automatically a same-cost replacement. No yield theorem follows from either.

The affine lift identity and uniform top-digit law pass for every permitted
composite modulus, including prime powers. Larger input representatives must
be retained at their necessary precision. R=2 passes; R=1 is excluded from
that lift theorem. The whole normalized output, not just the top digit, is
reconstructible from the acquired base plus the affine rule, because lower
digits remain fixed.

Adopt the lift review's scope repair: there is no ADDITIONAL response beyond
the acquired base and affine map. Base acquisition can still contain useful
information and is not erased by the simulation. Adaptive choices and batching
translate to the same public gcd arguments with base and consumer costs kept.
Consecutive inputs permit ordinary shifted-product batching; the simulation
does not lower-bound all such consumers. A full product gcd needs localization
even when no individual leaf is a full zero. The fixed-family equivalence is
not a theorem against other base selection, other observations, or factoring.

The separate `W032-joint-lift-coordinates.md` continuation is NOT covered by
these original scopes. It gives a proposed known-branch square coordinate and
joint-uniformity statement for all high lifts, awaiting its own review. The
canonical interval a<N remains a different distribution. No independent
CRT-root branch has been acquired by ordinary Hensel lifting.

The fixed assay and required project checks passed; see the separate assay
disposition. Shared checks do not prove these prose results. Neither accepting
the finite evidence nor the symbolic identities establishes a better factoring
bound. The next useful work is canonical-floor yield or an actual separating
cover generator, not another copy of the completed N=143/N=323 assay.
