# r147 — unresolved arithmetic boundary; zero nomination

## Target and source fidelity

Let phi=(1+sqrt(5))/2. Is the following set infinite?

    {P in Q[x]: P(Z) subset Z and |P(n)| <= phi^n for EVERY integer n>=0}.

This is the exact critical-prefactor-one question recorded in the introduction
of Avner Kiro and Alon Nishry, *Integer-valued polynomials satisfying growth
constraints*, Forum of Mathematics, Sigma14 (2026), e110,
DOI10.1017/fms.2026.10260. Actual publisher introduction, Theorems1.1/1.2,
Section3.1/3.2, Lemma4.10 and final Section6 argument were read, along with
the corresponding current arXiv2508.17335v1 sections. The live abstract history
lists only v1. The publisher gives publication20July2026. The journal still
states that this exact boundary is unknown. It proves infinitude with
prefactor sqrt(2phi)+epsilon, which does not imply prefactor one. Its related
weighted-square estimates concern different convex bodies. No source
normalization/typographical correction is offered as a discovery.

The original Dimitrov question, MathOverflow139140, and complete relevant
Elkies/Speyer answer bodies were retrieved. Speyer's 2013 proof handles rates
strictly on either side of phi, and explicitly loses the boundary through a
disk-radius margin. The comment asking about the boundary does not supply
a proof. The 2025 comment points to Kiro–Nishry. No later full resolution was
established by the bounded targeted public search. This is not a declaration
that the worldwide literature has none.

## Early duplicate and public screen

Ancestor and batch AGENTS, ledger, prior-campaign-context and current NEXT
were read; JSON accepted inventories were parsed. Counts9 additional/39 total,
next40 are observations only; no shared count edits. We reused the r144/r141
qualified original-role index, preserving its r133/r137 inheritance and
original r111–r113 science. New/changed originals were refreshed. Final screen
has1,563 retained original-role paths, no hit cutoff;155 build/replay/release
echo paths were explicitly classified and omitted. No giant unchanged
inventory was rebuilt. Full bodies, not snippets, were searched. Early broader
receipts before this echo-role refinement remain in alias-queries.jsonl.

Exact IDs/title/authors/claim aliases were queried before downloading the
selected primary source. Matching original bodies were reopened and retained
as sources/history-HASH.txt. The broad Dimitrov hits are S.I.Dimitrov's
arithmetic-ratio questions, not Vesselin Dimitrov's IVP question; the Speyer
hit in r85 concerns Schubert polynomials. The r144 power-monoid discussion
contains no IVP result. Repeated arithmetic proof/review files are duplicates
of the canonical mixed-arithmetic body. Those matches provide no previous
IVP theorem and were not treated as new science. No exact Kiro–Nishry/2508.17335
or boundary-question target match appeared in this retained scope.
Sequencing limit: the exact MathOverflow139140 numeric identifier was added
to the final alias query after retrieving that comparator. Its named
authors and boundary-claim aliases were screened before retrieval, but this
is not full compliance with the requested exact-ID-before-every-download order.

The preliminary power-monoid pool was stopped before a primary download:
2602.19493 and2607.23301 have public resolution announcements for the intended
automorphism questions; r144 had also identified the latter family. We do not
claim to have independently verified those public proof bodies here. There
is no nomination or reconstruction of that family, or of any excluded r144,
r141, r138, r137, r133 or r134 target.

## Mathematics: what fails at the boundary

Write P(x)=sum_{k=0}^d c_k binom(x,k), with c_k integers, and
h(w)=sum c_k w^k. The formal generating identity

    sum_{n>=0} P(n) z^n = h(z/(1-z))/(1-z)

follows by summing each binomial series. Put r=1/phi. The map w=z/(1-z)
sends |z|=r to the circle |w-r|=1: substituting z=w/(1+w) gives
|w|²=r²|1+w|², whose completion of the square has center r and radius1
using r²+r=1. This is the critical disk, so shrinking its radius to gain a
geometric series would change the target rate.

Here is an exact obstruction to a natural fixed-power route. For a
nonconstant integer polynomial h of degree d, write

    h(r+u)=sum a_j u^j.

Then a_d=c_d is a nonzero integer, and
a_(d-1)=c_(d-1)+d*r*c_d is nonzero, since r is irrational. Orthogonality
of u^j on |u|=1 gives

    mean_{theta} |h(r+exp(i theta))|² = sum |a_j|²
       >= c_d² + |c_(d-1)+d*r*c_d|² > 1.

Consequently sup on this circle is strictly greater than1 for EVERY such h.
Thus there is no nonconstant integer h whose powers h^m can be bounded by
one on the entire critical circle. This blocks the simple Cauchy-bound
version of the fixed-power/Fekete construction. It does NOT prove that the
coefficient sequences of h^m violate the desired inequalities: coefficient
cancellation is different from the sufficient circle-supremum estimate.
It does NOT refute the source question. This elementary control is uncredited.

The shifted-coefficient viewpoint also explains a rounding obstruction.
Starting with (w-r)^d and rounding the w coefficients from top to bottom
can introduce an error delta_j(w-r)^j at each step, |delta_j|<=1/2.
On the unit circle the triangle estimate is 1+d/2, and its orthogonal
mean-square estimate is at most1+d/4. Neither is a degree-independent
prefactor-one estimate. Below radius1 the same geometric sum decays after
a long initial gap; at radius1 the tail no longer decays. This identifies
the missing gain rather than extrapolating a strict-rate proof.

For comparison, the unscaled Gram matrix
M_jk=sum_n binom(n,j)binom(n,k)phi^(-2n) has determinant phi^(d+1).
Indeed Parseval and the above change of variables give phi times the
normalized circle moment matrix, whose monic orthogonal polynomials are
(w-r)^k with norm one. Its upper-triangular recentering has determinant1.
The corresponding l2 ellipsoid at radius1 has volume
Vol(B_2^(d+1))*phi^(-(d+1)/2), which tends to zero. Therefore a direct
Minkowski-volume argument on that inscribed ellipsoid cannot force the
desired unbounded degrees. A small-volume ellipsoid still can contain
lattice points, and the sup-norm body is larger: neither observation
settles finiteness. The published more refined body argument remains
strictly weaker than the selected prefactor-one question.

## Bounded exact diagnostics

checks.py performs integer LLL selection in dimensions3,5,7,9,11,13,17,21
(degree caps2,4,6,8,10,12,16,20), using at most131 weighted evaluation
coordinates. This is a heuristic candidate selector, not enumeration or an
optimality certificate. All returned rows are checked, including high-degree
rows; an initial run which checked only the first five rows is retained in
checks.log and superseded by checks-all.log and checks.json.

Each selected integer vector is a literal binomial-basis polynomial.
Finite comparisons are exact: for n>=1, floor(phi^n) equals L_n minus1
for even n and L_n for odd n, where L_n is the Lucas sequence. This follows
from L_n=phi^n+(-1/phi)^n. At n=0 the bound is1. There is no floating-point
tolerance in certification.

For a candidate of degree d let C=sum_k |c_k|/k! and N=max(64,64d).
For n>=N, |P(n)|<=C n^d. The checker verifies exactly

    C*N^d <= (3/2)^N,     (1+1/N)^d <= 3/2.

The second inequality ensures n^d/(3/2)^n is nonincreasing for n>=N;
the first therefore establishes the entire tail, since3/2<phi. Thus the
listed individual polynomials have all-n certificates, not just a tested
prefix. audit.py independently recomputes every prefix by iterating the
forward-difference table rather than evaluating binomial sums, and checks
the tail inequalities again. See independent-checks.json for the exact
deduplicated number and coefficient lists. The largest degree obtained is20.

These are a FINITE set of examples. They neither prove that degrees are
unbounded nor distinguish the finite/infinite alternatives. No degree case,
tail lemma, numerical lattice quality, or elementary circle obstruction is
a nominated discovery. No exhaustive low-degree census is claimed.

## Strongest objection, exact falsifiers and remaining bridge

Strongest objection: no full source answer has been obtained. There is no
uniform construction and no upper bound on the degrees of all admissible
polynomials. The source already gives a much stronger infinite-family
existence theorem at a larger prefactor than any finite list can establish.

An affirmative full solution requires, for every D, an admissible P with
degree>D. An equivalent negative solution requires a finite D bounding
the degree of every admissible P: for any fixed degree only finitely many
possibilities exist because P is determined by its bounded integer values
on0,...,D. A claimed positive construction is falsified by one integer n
with |P(n)|>floor(phi^n), or by bounded degrees across the asserted family.
A claimed universal degree bound is falsified by one all-n-certified
higher-degree polynomial. None of the finite controls alone settles either
universal assertion. No such full proof is present.

## Access, registry and freeze limits

Primary HTML bytes, URLs, actual retrieval UTC, hashes and lengths are in
http.jsonl/provenance.json. Public HTTP only; no tabs, accounts, uploads or
public actions. All four primary fetches returned200; no403/429 retry or
challenge bypass occurred in this lane. Web search receipts are bounded
discovery aids, not proof-body evidence. No exhaustive specialist database
or worldwide priority claim is made.

registry-screen.json reuses retained complete tree paths and bounded returned
deltas. The qualified Omega observation is490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c
at23:50UTC, with BOTH aa026->a19a and a19a->490f intervals capped300 paths.
r140 closes only its three named source-facing Markdown bodies in selected
scopes of the first interval. OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
is inherited unchanged. No badge/HEAD inference, head chasing, or semantic
current-proof clearance is claimed. Omitted deltas and unrelated theorem
names remain a material prior-art gap before any future nomination.

All helper processes use the unchanged required guard:512MiB AS and sampled
group RSS,210s CPU,230s wall, nominal40ms sampling. Sampling does not prove
continuous peak bounds. Mutable NEXT is a separately frozen context copy;
it is outside scientific-freeze.json. Finalmanifest covers the delivered
scientific, context and helper files with explicit non-self-reference
exclusions; manifest-verification.json verifies it.

ZERO. No PROOF.md, Lean, manuscript, review request, acceptance or count change.
