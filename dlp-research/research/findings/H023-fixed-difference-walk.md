# H023 fixed-difference walk: cheap translation, expensive unresolved escape

2026-10-08. Native Astra proposer and native Sol independent reviewer
COMPLETED. Root checked formulas, coefficient arithmetic and scoped dynamical
argument. No numerical run or Lean claim. Brief in H023-coordinate-walk-and-EDS-keys.
Known differential identities; no novelty assertion or verified solver gain.

## Representation and regular translation

For G=(g,yG), use u=x(P)-g,v=x(P-G)-g, with infinity sentinels. This
ordered pair determines P: the other possibility from its first abscissa is
-P, and equality of second abscissae then forces2G=O or2P=O. Odd prime
order excludes a nontrivial ambiguity. Reflection P->G-P swaps coordinates,
updating labels(a,b)->(1-a,-b). Sorting represents exactly(q+1)/2 classes.
This reflection is conjugate to ordinary negation by translation through G/2;
it offers no extra quotient-size gain over the competent negation baseline.

Let c1=2(3g²+A),c2=4yG². The ordinary addition abscissa identities give

    z=x(P+G)-g=(c1+c2/u)/u-v.

Regular translation sends the pair to(z,u), then sorts it with the label
reflection. It uses2M+I, excluding additions/dispatch. The selected batch
inverse gives5M+(I-3M)/n per translation for n active states. No S is hidden.
This is a concrete small arithmetic saving, not a useful-collision estimate.

## Exact pure-translation obstruction

For sorted u<=v, the next minimum min(z,u) cannot increase. If z>u, the
canonical successor represents -P, then its +G successor represents G-P,
the original reflection class. Labels cancel exactly on this regular two-cycle.
Boundary/known-point exceptions require dispatch and are not covered by that
fruitlessness statement.

The cyclic nearest-neighbor graph quotiented by P->G-P is a path with an
endpoint self-loop. Hence any DETERMINISTIC MEMORYLESS STATE-BASED choice
of only±G has directed cycles of length at most2. This does not cover
randomized/history-dependent policies or other paid jumps. A small state
space is therefore insufficient to justify a rho stopping law.

## Mixed operations and complete-cost gates

Doubling the represented point requires both x(2P) and x(2P-G). Direct
affine formulas are

    x(2P)=(3x²+A)² / (4*(x*(x²+A)+B)) - 2x,
    x(2P-G)=2*((x+x')*(x*x'+A)+2B)/(x-x')² - g,

where x'=x(P-G). Costs are2M+2S+I and3M+S+I respectively, including the
ordinary constant multiplications as specified, with small-integer multiples
counted as additions. Reviewer inspected the [primary EFD formulas](https://hyperelliptic.org/EFD/g1p/auto-shortw-xz.html).
Projective substitutes must also pay invariant key/canonicalization costs.

For a branch chosen BEFORE arithmetic, let rho be the OBSERVED doubling
fraction. Batching all n*(1+rho) denominators once gives per output

    5M+rho*(6M+3S)+(I-3M)/n.

Only assuming equal useful-collision constants to competent negation rho,
arithmetic saving needs rho<s/(6+3s),s=S/M. Ten-percent saving additionally
requires rho<(.9s-.5)/(6+3s), approximately .02619 at s=.8. A nominal hash
branch probability is not the observed frequency, nor a proved escape rule:
any translation two-cycle with two translation-selected states remains.

A concrete alternative computes +G first and doubles instead when z>u.
This is state-based and removes those identified pure-translation two-cycles.
It pays the discarded translation and a subsequent batch, giving leading
5M+rho*(11M+3S), plus the finite second-batch correction when escapes occur.
Its ten-percent gate at s=.8 is rho<.01642. No adequate escape-frequency
or useful-hit law has been established. Neither mixed rule is admitted as an
improved solver; other cycles/label failures and restart costs remain open.

## Exceptions, memory and decision

O/G involves infinity; zero shifted coordinates identify the known-log
{-G,2G} class; x=x' identifies G/2. Recover from affine labels when their
target coefficient is nonzero, otherwise pay dispatch/restart. Nonzero rational
points have no zero doubling denominator in the full odd-order group.

Whole-pair equality, not first-coordinate equality, establishes coalescence.
Use a fixed successor determined by the canonical pair, with compatible DP
checks. Full-state identification/equality may use paid records or hashes
with full verification; hash equality alone is insufficient. Compare labels,
active states, larger scratch batches, endpoints, seeds, failures, table work
and final scalar verification at matched memory. Neither state count nor
uniform marginals proves the ordinary rho constant.

Retain the exact representation and kernel as a possible component. Reject
translation-only mixing; park the mixed gain claim without the missing
frequency/useful-collision analysis. No prototype currently has a supported
complete-work rationale. A new escape schedule or explicit positive argument
for a bounded diagnostic could reopen it. No general coordinate-walk lower
bound follows; current verified ECDLP improvement remains NONE.

Endpoint refinement from the subsequent independent shifted-fold review:
H022-final-mechanism-scopes.md derives lambda=(u*v-(3g²+A))/(2yG) as an exact
one-field identifier of the H023 unordered pair, with a vertical sentinel.
It costs2M per endpoint after paid setup; active states remain two-field.
This is an alternative to storing both fields and does not change the mixing
gate or justify a complete-work gain. Whole-pair hashing may choose DPs.
