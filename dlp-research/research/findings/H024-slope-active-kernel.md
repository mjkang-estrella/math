# H024 slope-active translation kernel (pending independent review)

2026-10-08. Native Sol proposal; root derivation below; native Astra independent
review is RUNNING. This is a component hypothesis, not an improved ECDLP solver.
No numerical experiment or new Lean claim. Verified complete-work gain NONE.

## Proposed representation and exact coupling

Let E: y²=x³+Ax+B over F_p, p>3, with odd prime-order generator
G=(g,h), h nonzero. Use reflection R(P)=G−P, conjugate to ordinary negation.
For ordinary finite states put μ=(y(P)+h)/(x(P)−g). It is invariant under R;
the two shifted abscissae u,v are roots of

    T²+(3g−μ²)T+(3g²+A+2hμ)=0.

Canonicalize to u=min(u,v), using canonical field integer representatives;
the represented point is (g+u, μu−h). Thus μ alone is the exact orbit key,
while (μ,u) gives a two-field active state. Exceptional vertical/zero cases
require dispatch; do not apply an inverse to zero. See H023 for known-point
recovery, coefficient-zero restarts, and the exceptional reflection fixed point.

For +G, the ordinary secant slope is μ−2h/u. Therefore

    μ' = −μ+2h/u,
    z = μ'²−3g−u,
    u' = min(z,u).

If z<=u the labels (a,b) become (a+1,b); if z>u the reflected output is −P,
with labels (−a,−b). Equality/fixed-point dispatch must be specified separately.
The new other root is transiently available. Compute a preexisting deterministic
pair-based branch/DP predicate at state creation and retain its finite flag.
This preserves that walk's choices without recomputing v from μ on every step.
Hashing μ instead is a different walk, not an automatic collision-law coupling.
Endpoint equality may use μ, already active, avoiding the old pair representation's
2M endpoint conversion. Seeds, flags, labels and records still cost space/work.

## Proposed operation ledger

M,S,I count base-field multiplication, squaring and inversion. Fixed constants
are prepared and charged. Additions, comparisons, hashing and memory are outside
this arithmetic subtotal, not free in a full solver.

Regular kernel: 1M+S+I; an n-way nonzero batch costs
n(4M+S)+(I−3M). This improves the former pair kernel 5M per step only when
S<M, before other costs. It does not change its fruitless-cycle dynamics.

Branch-before-step doubling: recover y (1M); ordinary affine doubling
(2M+2S+I); compute new μ (1M+I); compute other root (1S).
Total 4M+3S+2I. The second inverse depends on the first output, so for n walkers
of which d double, the proposed finite ledger is

    n(4M+S)+d(6M+2S)+(1+1[d>0])(I−3M).

This requires TWO dependent batches when d>0. It is not a one-pass inverse
batch. Under an unproved equal-useful-collision-law assumption, a 10% arithmetic
saving against 5M+S at s=S/M=.8 requires d/n < .42/7.6 ≈ .05526,
before all other costs. A rare hash coin is not an adequate cycle escape rule.

Root's additional UNREVIEWED jump subtotal: recover y (1M), add precomputed
J (2M+S+I), normalize μ (1M+I), compute other root (1S), hence
4M+2S+2I, or leading 10M+2S after two dependent inverse batches.
Table construction, labels, exceptions and jump selection are additional.

If translation is computed first and discarded at a detected reversal, charge
that work. Leading totals become 4M+S+rho(10M+3S) for doubling or
4M+S+rho(10M+2S) for the proposed arbitrary jump. At s=.8 the conditional
10% thresholds are respectively .42/12.4≈.03387 and .42/11.6≈.03621.
Detected-then-doubling uses THREE successive inverse batches when escapes occur;
its finite arithmetic subtotal is n(4M+S)+d(10M+3S)
+(1+2*1[d>0])(I−3M). These are necessary arithmetic gates under the stipulated hit law, not
predictions of actual escape frequency, useful collisions, or wall time.

## Independent initial escape proposal and scope correction

Native Astra's initial H024 proposal recovers y from the OLD paired-x state
in3M, then computes x(P+J) and x(P+J−G) in2M+2S+2I:
5M+2S+2I total, with two independent denominators. Its proposed detected-reversal
schedule pays the discarded old 5M translation plus leading11M+2S per escape.
It has no positive reason for the required long descent segments. This is a
separate old-representation component proposal, not the active-slope cost above.

Centered multiplication T=P−G/2 gives T_i=c_i T_0. A signed repeat WITHIN one
nonzero seed forces c_i=±c_j and its label equation is tautological. This does
not exclude useful cross-seed collisions; reseeding, orbit coverage and discovery
must be paid. History/orientation-expanded states do not inherit quotient-state
coalescence merely because their slope keys agree.

## Decision gate / next work

Independently verify formulas, canonical labels, exceptions and dependent-batch
costs. Then freeze a concrete escape rule and a bounded synthetic diagnostic of
actual escape frequency and useful collisions over increasing sizes/seeds. A
kernel saving alone cannot justify a full benchmark campaign. No accepted
positive full-solver rationale or exponent change yet. Independent algebraic
and information ideation remains live, without anchoring it on this proposal.

These gates concern a matched low-memory rho objective only. At s=.8, even
the zero-escape optimistic rho coefficient is sqrt(pi/4)*4.8≈4.254, versus
(2sqrt(2)/3)*3.3≈3.111 for the accepted high-memory H019 x-only BSGS
coefficient. The different memory budgets must not be conflated.

## Other independent Sol mechanisms (delivered, scoped)

Centered scalar maps: H=G/2, T=P−H; a scalar-affine map tP+sG
commutes with reflection precisely when t+2s=1, becoming T→tT.
X-only doubling costs2M+2S+I, batched5M+2S, with no advantageous
per-step ledger. For fixed doubling cross-seed lists of length L, ratios
are ±2^(i−j), at most2(2L−1) distinct values, not L² independent
opportunities. This is a screen of fixed doubling lists, not every
coordinate-dependent scalar-map schedule. A concrete cross-seed coverage
construction remains missing; no numerical run admitted.

Isogeny/model transport: a rational isogeny with degree coprime to q
preserves the scalar on the q-subgroup, but construction, evaluation,
conversion and destination search are paid. No destination with a better
complete cost was identified. Full odd rational group order precludes a
rational degree-two isogeny (its nonzero kernel point would be rational
2-torsion); rational odd-degree isogenies with nonrational kernel points
are not excluded. No novelty or universal transport lower bound claimed.

Sol reports direct inspection of primary sources, not root re-verification:
[EFD affine formulas](https://hyperelliptic.org/EFD/g1p/auto-shortw.html)
and [Sutherland Lecture4, sections4.2–4.3.2/Lemma4.26](https://math.mit.edu/classes/18.783/2023/LectureNotes4.pdf).
These support ordinary addition/duplication and isogeny framework; the
candidate-specific representation and costs are project derivations.
