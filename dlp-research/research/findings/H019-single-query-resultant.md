# H019: a real single-query product evaluator, no improved detector

2026-10-08. Root's primary-literature followup to the missing divisor/norm
operation. Native Astra /root/h007_additive_relations independently checked
the identity, exceptions and source; native Sol /root/h010_early_dependencies
completed the full-work comparison separately; root integrated both reviews. No numerical work, files from
reviewers, or new Lean claims. This is known algebra applied to our candidate,
not a claimed discovery or ECDLP improvement.

## Source and precise extension

Root and Astra read Lemmas4.3/4.9, Algorithm2 and Theorem4.11 in
[Bernstein–De Feo–Leroux–Smith](https://arxiv.org/pdf/2003.10118).
The paper evaluates structured elliptic products at one point using smaller
polynomials and a resultant. Its complexity counts field operations and pays
for input-point generation separately. The algebra-extension discussion does
not supply cost-independent batching. The publisher-project PDF fetch failed
with502; the arXiv PDF succeeded. Older H002 findings concerned a full-kernel
isogeny/surface application, not this arbitrary-list evaluation question.

Our application: let u_i=x(A_i),v_j=x(B_j) on y²=x³+ax+b in characteristic>3.
Use the standard third summation polynomial

    S3(u,v,z)=(u-v)²z²-2((u+v)(uv+a)+2b)z+(uv-a)²-4b(u+v).

Set H_A(X)=product_i(X-u_i), R_alpha(X)=product_j S3(X,v_j,alpha).
The monic-resultant identity gives

    D(alpha)=Res_X(H_A,R_alpha)=product_(i,j) S3(u_i,v_j,alpha).

This identity needs explicit coordinates, not their scalar logs or an injective
index system. Repeated sums contribute multiplicities. Build R_alpha from
quadratic factors, evaluate it on all u_i with monic remainder trees, then
multiply: soft-O(|A|+|B|) field work per query and soft-linear storage.
Precompute H_A and its tree; retain normalization, generation and labels as
paid work. Empty products are handled explicitly with constant work.

For cross-distinct abscissae, D equals the product of
(alpha-x(A_i+B_j))(alpha-x(A_i-B_j)) times
Delta=product_(i,j)(u_i-v_j)². For detection DO NOT divide by Delta.
At u=v, S3(u,u,alpha)=-4(u³+au+b)(alpha-x(2A)). On a nonzero odd-order
subgroup the coefficient is nonzero, so the finite doubled-point case is
handled correctly even though the normalized quotient is undefined.
No rational-function pole cancellation is introduced.

Retaining the multipoint values identifies a zero row; a one-list scan finds
a zero factor. Test signs on actual points, combine labels, require a nonzero
target coefficient and verify the scalar. Extraction costs soft-O(|A|+|B|)
plus the final verification. A zero with only useless label relations is not
a solved target.

## The unfilled cost requirement

At r arbitrary third-list coordinates, separate evaluation costs
soft-O(r(|A|+|B|)). Running the same monic-tree construction over
Fp[T]/C(T),degC=r, with alpha=T has the same base-field bound under ordinary
quotient-ring arithmetic. The literal ring implementation can store quadratic
data; sequential evaluation needs only soft-linear storage. For three lists
of size n, this remains soft-O(n²), missing the sub-n^(3/2) target.
This is the cost of the specified algorithms, not a lower bound for every
joint evaluator. A one-point signed-pair dictionary search already has linear
group cost, so the known evaluator is not a new single-query exponent gain.

Each pair produces at most two abscissa classes, representing at most four
nonzero points. Thus two fixed lists of sizes a,b cover at most4ab scalar
values for an all-sign membership query, capped by q. Do not confuse2ab root
classes with2ab uniformly sampled scalars. Actual duplicates reduce coverage;
target-coefficient usefulness requires separate analysis.

No new experiment admitted by the identity alone. A joint zero-support
algorithm below the balanced n^(3/2) threshold, with extraction and setup
paid, or a substantiated material complete-cost saving could reopen it.
The accepted square-root reference and verified-improvement NONE remain.

## Independent complete-work review

For balanced lists n with optimistic useful coverage Theta(min(q,n²)), the
literal advertised query schedule costs softO(n+max(n,q/n)) for one target,
including setup and successful extraction. Its best scale is square root.
This conditional schedule estimate does not turn a softO upper bound into a
universal query lower bound. Duplicates and useless labels only reduce the
assumed coverage; generation, normalization, shifts and verification are extra.

Unequal sizes strengthen the comparator: store the larger list a, scan b
with both signs per query. Work a+b+b*max(1,q/(ab)) becomes a+b+q/a in the
sparse regime, matching the usual charged dictionary/BSGS tradeoff. The
max-size resultant query has no demonstrated improvement over this comparator.

For K targets, separate balanced resultant queries cost about
n+K*max(n,q/n), optimized near sqrt(q); sharing this setup alone does not reach
the known softsqrt(Kq) many-target tradeoff. This corrects the tempting but
wrong extrapolation n+Kq/n beyond n²~q: every query still pays for its list.
An interval-membership bisection costing softsqrt(interval-length) per level
also sums to softsqrt(q) over full-range search. Explicit pair storage costs
ab records and reverts to the ordinary table accounting.

Sol independently read the primary single-query theorem; Astra supplied the
arbitrary-list extension and exception proof; root checked both. No predicted
asymptotic or material complete-work improvement, and no new experiment.
