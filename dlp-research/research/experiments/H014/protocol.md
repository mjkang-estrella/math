# H014: exact tiny public-feature correlation screen, pre-run protocol

2026-10-08. Purpose: cheaply test two explicit possible information sources for
H013-MCL. No solver advantage or asymptotic correlation is assumed. Initial
screen may be speculative; a proof of correlation is not a prerequisite.
Root owns this protocol; separate writer owns character_screen.py. No numerical
execution until root reads code and independent preflight. No warmups/retries.

## Frozen family and admission

Fields p=59,101,251 in this order. Trial-divide p. For each field examine at
most256 lexicographically ordered pairs(a,b),1<=a,b<p, for y^2=x^3+a*x+b.
Pay square-multiplicity-table construction and every candidate point count;
skip singular curves. Admit the FIRST with full prime order q, q!=p,
q congruent7 mod12. Trial-division certification, not a prime/point-count oracle.
If none is admitted within256, mark that field INCOMPLETE and continue the next
frozen field, without replacement or any reset of the GLOBAL budget. All attempted
curves and counts are retained. Admission is independent of measured features.
Nonzero a,b exclude j0/1728; full odd prime order is ordinary in these fields.
Hasse intervals are disjoint, so admitted q increase. These are deliberately
tiny general curves, not representative evidence for cryptographic sizes.
Pre-run review replaced p43: its only admitted nonanomalous order would be31,
giving Frobenius discriminant13^2-4*43=-3 and hence j0, forbidden by a!=0.
For p59 the compatible order67 has discriminant(-7)^2-4*59=-187, so that
particular impossibility is absent; admission within the window remains unproved.
This revision occurred BEFORE any numerical run, not after selecting outcomes.

Enumerate points of an admitted curve using the charged square-root lists
already built. Choose lexicographically first affine G0. Verify qG0=O with no
earlier orbit closure, every generated point on curve, and full orbit uniqueness.
Prime q and nonzero G0 certify full order. No discrete-log table goes to a solver:
there is no solver here. Diagnostic enumeration is fully charged and disclosed.

## Paid exact character and two public features

Factor q-1 by trial division. Find the least primitive scalar generator g by
testing g^((q-1)/ell)!=1 for every prime divisor ell. Set h=(q-1)/6 and z=g^h.
Construct and verify six distinct powers z^j. The complex character chi(n) is
0 at n0; otherwise map n^h through this six-entry phase map to zeta^j, where
zeta=exp(pi*i/3). Modular exponentiation is explicit binary arithmetic, no
uncounted pow/inverse/discrete-log oracle. Everything above is charged setup.
Explicitly verify chi(g)=zeta and chi(q-1)=-1.

Represent Z[zeta] exactly by integer pairs(A,B) with zeta^2=zeta-1. Powers are
(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1). Conjugation sends(A,B) to(A+B,-B).
Multiplication sends(A,B),(C,D) to(AC-BD,AD+BC+BD). Squared complex norm is
A^2+A*B+B^2. Character values are exact; no FFT or floating point.

Freeze center_p(t)=t for0<=t<=floor(p/2), otherwise t-p. Public features:

- f_sign(P)=sign(center_p(y(P))), represented as(integer,0).
- f_par(P)=chi(center_p(-x(P)/y(P)) modq), zero allowed.

O maps to0. On admitted full odd-order curves finite y!=0. Evaluate the inverse
by explicit exponentiation with an inverse verification; count feature work
separately from cached diagnostic reads. This formal parameter has no established
finite-field approximate-linearity property. Symmetry alone does not imply signal.
Both features satisfy f(-P)=-f(P), since h odd gives chi(-1)=-1.

## Complete-domain measurements and frozen controls

Enumerate the nonzero orbits of G0,2G0,-G0 independently, paying all additions.
For each report S=sum_(n=1..q-1) f(nG)*conj chi(n), pair(A,B), denominator q-1,
and squared magnitude numerator A^2+AB+B^2 over(q-1)^2. Retain zero-feature
counts and per-point rows. Cache public features once per actual point for THIS
diagnostic; do not use lookup cost as proposed online feature cost.

Check the exact identities S(2G0)=chi(2)*S(G0), S(-G0)=-S(G0), and pointwise
feature negation. These generator variants are deterministic controls, NOT
independent curve samples or generalization successes.

Build a planted point-indexed control ONCE: fplant(nG0)=chi(n). Keep it fixed
when changing generators. Its three sums must equal(q-1), (q-1)*chi(2), and
-(q-1). It knows the diagnostic labels; explicitly NOT a public predictor.
Also compute the even control sign(center_p(x(P))) and require its correlation
to vanish on every complete orbit. This parity null is exact, not a random test.

On the G0 orbit use three ODD-PRESERVING signed-pair label permutations with
seeds7,19,43. Reset each seed per curve. Fisher--Yates shuffle the representatives
1..(q-1)/2, then give each pair an independently drawn orientation bit. If the
assigned signed label for n is d, assign q-d to q-n. Evaluate conjugate chi of
these labels against the fixed point sequence. The SAME permutation serves both
features; report every output, never select a favorable seed. Full unpaired
permutations would erase the known odd symmetry and give a misleading null scale.
Cache the public/even-control values once per point; planted table stays separate.

Freeze 32-bit LCG state <- (1664525*state+1013904223) mod2^32, then output
word=state XOR (state>>16). This output transform is a bijection of32-bit words;
it avoids the raw LCG's deterministically alternating least bit. This correction
is frozen BEFORE any run. Bounded draw rejects words>=floor(2^32/bound)*bound,
then reduces modulo bound; orientations use bound2. Charge explicit arithmetic,
shift/XOR/rejections/swaps. This PRNG is a reproducible
descriptive control, not independent true randomness. Under the SEPARATE ideal
model of uniform signed-pair permutations, the mean correlation is0 and its
exact second moment is 2*sum_(all nonzero P)|f(P)|^2/(q-1)^2. Report this rational
reference and a predeclared descriptive flag |c|^2>9*that value (3 RMS), not a
p-value or a significant discovery. No normalization assumed when f has zeros.
A deterministic PRNG permutation control
is not an iid sampling theorem or a p-value. No feature/sign/seed winner selection.

## One global cap and event model

Start ledger/time before field certification or algorithm table allocation.
One total1,000,000 instrumented events and60seconds, including all failed
candidate counts, setup, certification, feature arithmetic, orbit checks,
character conversion, caches and controls. No resets or independent pilot.
Stop on first exhausted limit and preserve completed/partial phase records.
Correctness failures stop the diagnostic, never ordinary rejected observations.

Use the H005-style explicit event model: integer arithmetic/remainders/bit
operations/comparisons, field arithmetic plus reductions, group calls plus
actual field operations, loop iterations, algorithm-table reads/writes and
initialization entries. Inversions/powers count calls AND actual operations;
these nested categories are not a weighted CPU-time total. Declare any exclusions
precisely (interpreter dispatch, ledger bookkeeping, serialization/source hashing,
tuple unpacking/ordinary assignments). PRNG, selection and mathematical loops
cannot be excluded as metadata. Report phase/category vectors, total, observed
wall time and storage entries. A syntax check is allowed before numerical run;
no importing the program to execute hidden tests. Final hashing/output may be
outside arithmetic timer only if explicitly reported. This is not a bit-cost or
GPU/CPU throughput benchmark. No dependencies beyond Python standard library.

## Interpretation and complete-cost relevance

H002 tested EDS predicates against integer parity; these are different features
against multiplicative characters. The earlier m2 proposal was NOT run: when
q=3 mod4 its coset has(q-1)/2 points, offering no cardinality reduction over the
known negation quotient. Here m6 gives h=(q-1)/6, nominally one third of that
domain. This is only a potential square-root-of-three cardinality factor; scalar
multiplication, calibration and feature work may erase it. Fixed m6 does not
overcome asymptotically growing fixed-base scalar-evaluation cost in the proposed
backend. A positive tiny signal is only grounds to investigate a feature family
with useful m and complete costs, not evidence of a full-size speedup.

Report exact values with controls, not a fitted exponent or a statistical
discovery. A null/weak signal concerns these curves/features only. A positive
signal still needs independent larger-curve validation and a complete gate
C_attempt<s*W_baseline, retaining failure costs and a competent signed baseline.
Exhaustive enumeration costs Omega(q) and itself is not a faster algorithm.
The main verified improvement remains NONE regardless of this diagnostic's result.
