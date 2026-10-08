# H015 source bridges: missing algorithms, not universal impossibility

2026-10-08. Substantive Claude Opus replacement report retained in
H015-primary-bridges-opus-raw.md. Root separately checks Cards C/D; native Astra
reviews A/B. No experiments, improved solver or new Lean claims. Raw extensions
are not accepted merely because they appear beside primary-source citations.

## C: fixed-characteristic finite-field algorithms

Root read [Kleinjung--Wesolowski, Theorem1.1](https://arxiv.org/pdf/1906.10668)
directly, beyond the proposer's abstract/snippet. For F_(p^n)^*, the theorem gives
expected time (p*n)^(2*log2(n)+O(1)). Here the base is the PRODUCT p*n, not p^n.
With p fixed this is quasipolynomial in n. The theorem does not supply an
efficient conversion of ordinary E(Fp) discrete logs into that favorable family.
Invoking it with growing characteristic p does not establish a sub-square-root
ECDLP cost. Its use of elliptic models for FIELD arithmetic must not be confused
with solving the group law's ECDLP.

Accepted scope: p-Frobenius is the identity on E(Fp) points, so merely evaluating
it on a target supplies no new scalar information. Missing is an actual paid
representation/descent/recovery bridge with controlled total cost.

Corrections to raw generalizations: pairing embedding degree is ord_q(p), a
divisor of q-1, not universally asymptotic to q. The given hypotheses do not
establish that order. An endomorphism preserving <G> acts by some scalar, but
its scalar need not be GIVEN or efficiently recovered from arbitrary point
evaluation; known efficiently represented endomorphisms are separate inputs.
No universal no-transfer theorem follows from either raw assertion. Known
special pairing-friendly families do not by themselves settle the ordinary
full-size challenge. No concrete improved transfer was supplied here.

## D: torsion lifts, gonality and the limits of degree arguments

Root read [Abramovich, Theorem0.1 and §2.1](https://arxiv.org/pdf/alg-geom/9609012)
directly. The result bounds complex gonality below by(7/800) times the congruence
subgroup index; for X1(q) this has quadratic order. The paper also explains the
number-field implication from infinitely many fixed-degree points to gonality
at most twice that degree. Finiteness of exceptional low-degree points is NOT
their absence, an effective construction-time bound, or a proof they cannot
reduce to some desired finite-field instances. Quantifiers in q, the base number
field, the chosen lift and the prescribed reduction must be kept separate.

A map-to-P1 fibre construction faces the gonality degree constraint. That is
not a lower bound on every method of constructing a closed point, or on every
compact arithmetic representation of a high-degree object. The raw universal
rejection based on a q^2-scale degree is therefore not accepted.

Root also read [Silverman's global torsion-lift slides](https://maths.ucd.ie/~gmg/ECC2007Talks/ECC4FacesOfLifts.pdf),
including the displayed Serre discussion. It establishes prior-art context for
lifting torsion to number fields. The nearby q^4 scale must not be adopted as
a precise single-point field-degree statement without distinguishing full
torsion from one vector.

Our elementary orbit check: if a fixed characteristic-zero curve has surjective
mod-q Galois image GL2(Fq), the full q-torsion field has degree
(q^2-1)*(q^2-q). The stabilizer of a fixed nonzero vector has q*(q-1) elements,
so the field of ONE nonzero q-torsion point has degree q^2-1 instead. Finite-index
variants require their actual image, and constants for a fixed curve cannot be
silently made uniform over adaptively chosen lifts. No arbitrary-point q^4
lower bound is accepted from the raw report/slide wording.

The supplied torsion card still lacks a cheaper way to construct the required
target-compatible global point, control its representation/height and precision,
and perform a full recovery within budget. Calling complex elliptic logarithms
after granting that missing object is not a verified improvement. Park as an
unspecified bridge, not a theorem excluding all global torsion-lift algorithms.

## A: corrected signature-duality hypotheses

Native Astra independently read [Huang--Raskind, §§5–6](https://arxiv.org/pdf/0710.2363);
root checked Propositions4–5 and the local/discriminant passages. The construction
uses rank one over Q for both the curve and its twist, giving rank TWO over K.
It assumes trivial ell-primary Sha and the stated localization isomorphism (or
its specified two-dimensional-image replacement); the algorithmic equivalence
has a heuristic direction. The raw rank-one-over-K summary was incorrect.
Unramified classes at good places vanish. Useful good places away from ell
require ell dividing the reduced curve order; Hasse gives norm at least
(sqrt(ell)-1)^2. Bad-place noncontribution uses additional hypotheses/heuristics.
The source's p^8 is an UPPER discriminant-size scale for selected lifts, not
conductor approximately p^8 or a runtime lower bound.

The review rejects the raw claim that duality classifies every algorithm as
Xedni or full ell-descent. Even the cyclotomic degree over K is
(ell-1)/[K intersect Q(mu_ell):Q], not always ell-1. Explicit field materialization
can be expensive without excluding all implicit representations. Large integral
valuations constrain ordinary encodings, not every algorithm; the asserted
anomalous-reduction search cost was unsupported.

Missing primitive: construct useful test classes/signatures with specified
representation, paid local pairings and a nonzero independent recovery coefficient.
A cheap paper gate would list contributing places and apply the local vanishing
tests. No such producer was supplied; park it without a universal rejection.

## B: surface specialization with the correct origin and rank bounds

The [Schuett--Shioda source, §§6.10–6.11](https://arxiv.org/pdf/0907.0298)
distinguishes complex Hodge bounds from the general Igusa bound. For the stated
elliptic surfaces over P1, rho<=12*chi-2 yields Mordell--Weil rank<=12*chi-4
before reducible-fibre deductions. The raw10*chi-2 ceiling is not valid
indiscriminately in positive characteristic. Rational elliptic surfaces retain
the rank-eight ceiling. Root read these source inequalities independently.

Reviewer-normalized pencil identity: on a smooth fibre with origin O, put
h=[H|_E-3O] in Pic0(E). For section D=eH-sum m_i E_i, its fibre intersection
degree is3e-sum m_i=1. When the exceptional restrictions are the indicated p_i,

    [D|_E-O] = e*h - sum m_i*[p_i-O].

This follows by degree-zero divisor arithmetic; it does not give the individual
logs or an algorithmic lower bound on exploiting auxiliary geometry. Rho is a
comparator upper bound, not proof this kernel search must cost sqrt(q). Global
intersection numbers do not by themselves reveal the local contribution at one
chosen fibre. Rational nonzero2-torsion excludes an odd-order GOOD fibre in odd
characteristic because prime-to-characteristic torsion survives good reduction.

Missing primitive: a specified section/search operation producing useful
specialization-kernel vectors with bounded section size, paid construction,
success law and independent target coefficient. No such operation was supplied.
An actual surface/search rule is a meaningful preflight; a blanket demand for
an already faster relation solver is not a cheap falsifier.

## Remaining source gap and disposition

The revised official2024/1330 landing page has five authors (Feng, Luo, Chen,
Nitaj, Pan), as already recorded in H013. Root's bounded PDF retry still failed:

```
set -o pipefail
curl --fail --location --max-time 20 --show-error --silent https://eprint.iacr.org/2024/1330.pdf | pdftotext -layout - - | head -70
```

HTTP403, empty PDF stream, exit1. Web click also returned an internal error.
No unread small-root theorem is adopted, and no recurring retry or numerical
pilot is warranted merely by this access failure. The primary report supplied
no executable improved bridge. Retain scoped source restrictions and the missing
operations; remove its broader impossibility conclusions. Main metric unchanged.
