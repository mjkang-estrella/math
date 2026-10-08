# H017 hybrid review: valid local screens, rejected global obstructions

Status: paper analysis, independently reviewed; no new solver, numerical run,
Lean claim or verified improvement. The raw Grok report is preserved separately.
Ordinary prime-field prime-order ECDLP retains the classical square-root working
reference, with applicable known automorphisms and complete costs charged.

## Ownership and evidence

Initial proposer: Grok4.7, retained T3 task suffix
`ecdloop-h017-computational-hybrids-grok-20261008-r1`; full task prefix and brief
are in H017-independent-briefs.md. Terminal summary read, no pending child runs.
Native Astra `/root/h007_additive_relations` independently reviewed cards1/3;
native Sol `/root/h010_early_dependencies` reviewed card4. Root reviewed card2,
checked the mathematical corrections and read the primary sources below.
All reviews read-only; root integrates. No experimental commands or seeds.

## 1. Algebraic fibres: a coverage bound is not a branch-search lower bound

For a rational function f of fixed degree d, the nonzero function
`h_nm(P)=f([n]P+[m]G)-f(P)` has pole degree at most d(n²+1), for n nonzero.
Its zero set has at most that many geometric points. Summing over predeclared
|n|,|m|≤N gives O(d N^4) covered points, **excluding identities**. This does not
prove that an adaptive algorithm must enumerate N² branches or take linear
time in n: scalar multiplication uses addition chains.

Identity exceptions matter. For f(P)=x(P)+x(P+G), f(-P-G)=f(P) identically.
Also a public coordinate predicate can choose R=P or R=-P, preserving f=x and
updating affine labels correctly, while the piecewise rule is not a morphism.
It gives no new gain, but disproves the raw global-morphism requirement.
Positive density alone does not force a morphism without an applicable degree
bound smaller than the number of agreements.

Two distinct reflections P↦-P+T compose to a nonzero translation. A key invariant
under BOTH everywhere is constant on the prime-order group. This statement does
not exclude partial, history-dependent or branch-selecting methods. Ordinary
prime-order does not imply Aut={±1}: j=0 permits the known cubic automorphism
where defined. Such constants belong in the matched baseline.

Disposition: keep the scoped zero-count screen. Reject the purported universal
label obstruction and mandatory square-root arithmetic cost. No explicit cheap
new branch with useful labels was supplied; no experiment admitted.

## 2. Pair dictionaries: repair the actual query before costing it

Let H2 have U distinct pair-sum abscissae. One fixed slice S3(a,Z,r) checks only
one a, not all decompositions. An explicit repaired query forms

    R_r(Z) = product over a in roots(H2) of S3(a,Z,r),
    gcd(R_r,H2), followed by a factor-tree search or scan for a witness.

Its degree is at most2U. Ordinary product/gcd computation uses soft-O(U) field
work per query; the literal product reads U factors. This is an available
algorithm, not a universal query lower bound after arbitrary preprocessing.
An implementation must retain signs, labels and exceptional-point handling.
With R=uG+vQ, v≠0, a verified signed pair decomposition gives the scalar by
subtracting u and dividing by v; known-log base entries alone have b=0 and
cannot supply the raw report's target coefficient.

Even U distinct values may require B² construction attempts from B base points;
setup cannot be called Θ(U) group additions without a generation argument.
For a fixed secret-independent dictionary and fresh uniform R, the signed
two-entry coverage is at most O(U²) group elements. Thus success per query is
at most O(U²/q). Charging U entries at setup and Ω(U) work for this literal
factor-reading query gives Ω(U+q/U) for U≤sqrt(q); for U≥sqrt(q) setup alone
reaches that scale. This screens the explicit operation only. Adaptive queries,
implicit data structures and alternative batched operations remain outside it.
Field-operation counts cannot be compared to rho additions to claim a lost
constant. Euclidean remainder-sequence length is neither a full half-gcd ledger
nor an asymptotic empirical test. No subresultant experiment admitted.

## 3. Growing anchors: the proposed lower bound has counterexamples

The frontier identity is ΔF=1-2Δc-h. A cycle closure with Δc=1,h=0 decreases the
frontier without a new anchor hit. Also colour1's translated two-anchor point
V=3Q-Br-Bs and colour0's U=-Ai-Aj can meet with
`3Q=Br+Bs-Ai-Aj`, retaining a nonzero target coefficient for q>3. Thus neither
"frontier decrease requires an accidental anchor" nor "all two-anchor rows
have zero target coefficient" holds. This does not make the selector efficient.

The claimed Θ(L/q) hit rate is unproved for adaptive geometric selection.
The displayed κq/L+L log(q) inequality is conditional on justified hit/stopping,
setup and per-row costs; κ≥1 is not automatic, and L log(q) counts elementary
group work in a simple setup, not L log(q) scalar multiplications. Signed sums
of interval anchors [j]G with coefficients in{-1,0,1} do have O(L²) possible
numerators; this is a support statement with its denominator/offset conditions,
not a universal search-time bound.

Disposition: raw lower bound rejected. The earlier fixed-table coverage screen
and explicit closure equations remain valid at their stated scopes. No new
paid selector or positive evidence warrants an experiment.

## 4. Doubling side collisions: storage defeats the advertised schedule

If 2Pi=sPj, s∈{±1}, the correct recovery equation is
`(2bi-s bj)k=s aj-2ai (mod q)`; require a nonzero coefficient and verify kG=Q.
For iid nonzero points, quotient by negation has N=(q-1)/2 classes. For q>5,
the three per-pair events Pi=±Pj, 2Pi=±Pj, Pi=±2Pj are disjoint, each with
probability1/N. Doubling an arrival and looking up old ordinary keys adds one
channel (factor2 in expected pair count). Both directions give factor3, not4,
and need additional keys/lookups or an equivalent specified schedule.
Independent uniform affine labels and coordinate-only selection give useful
denominator probability1-1/q; actual walk-derived labels require analysis.

Pair counts alone do not establish sqrt(2) or sqrt(3) first-hit gains. Those
constants require a birthday/Poisson approximation or a proved hitting law.
More seriously, ordinary distinguished-point storage cannot recover all side
collisions: F(2P) generally differs from2F(P), so these collisions need not merge
walks. Under ideal iid sampling, retaining a θ fraction of old points captures
only θ/N directed doubling hits per pair. This count is not a whole-walk speed
factor. Storing every point changes memory, traffic and the matched baseline.

Only after proving an effective detected rate r and the corresponding first-hit
law is the steady-state necessary cost gate
`Cextra/Cstep < sqrt(r)-1`, with setup/failures/capacity charged separately.
One literal arithmetic schedule already fails this gate: affine x-only doubling
with z=3x²+a, λ=z/(2y), x2=λ²-2x, sharing one global standard batch inversion
but no further intermediates, adds4M+2S per point. Compared with literal affine
addition5M+S, its ratio is≥0.8, exceeding both sqrt(2)-1 and sqrt(3)-1. This
screens that arithmetic ledger only, not all implementations or complete work
with unknown memory weights/sharing. No hardware measurement is claimed.

Next gate, if this route is reopened: specify the detection/store policy and
matched complete ledger. A standalone doubling benchmark would not fix the
endpoint-detection defect. Pair-enumerating triple reporters remain the earlier
q^(2/3) method, not a lower bound for every implicit detector.

## Primary-source check of the proposed geometry transfer

[Alman–Vassilevska Williams, arXiv:2610.06783](https://arxiv.org/pdf/2610.06783),
v1 October5,2026: root read the abstract, Theorems1/3 and the consequences on
pages9–11. The paper reports integer3SUM time n^1.9992. Its lopsided product
theorem takes a specified set of requested positions; it does not discover
unknown zero positions. The fixed dimension3 in SP3 yields no exponent saving
from its dimension-dependent factor. The discussion of problems merely known
3SUM-hard does not supply a collinearity algorithm. A new small, success-
preserving finite-field reduction is still needed. This is a source-scope
check, not an audit of the entire recent paper or a proof excluding such a bridge.

[Aronov–Ezra–Sharir](https://arxiv.org/pdf/2003.09533): root read the introduction,
decision-tree discussion and relevant theorem context. The n^(24/13+ε) bound
counts constant-degree polynomial sign tests, not ordinary orientation tests
or an executable finite-field solver. Even a hypothetical unit-field-cost
transfer would yield q^(8/13+ε), above the working square-root reference, but
that upper bound is not a lower bound for other reporters. Neither source
changes the missing SP3 sub-n^(3/2) detector requirement.

## Verdict

No measured or asymptotic improvement. Four mechanisms retained with corrected
limits; several claimed impossibility arguments explicitly rejected. No broader
Lean machinery or numerical run is justified by these outputs. The still-useful
open questions are concrete implicit relation detection, useful adaptive anchor
selection, or a fully specified cheaper side-collision protocol, not the false
universal lower bounds above.
