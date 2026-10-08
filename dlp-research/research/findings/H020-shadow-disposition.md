# H020 signed macro-walk: gain-bearing primitive undefined

2026-10-08. Grok proposal and independent Claude Opus review retained verbatim
in H020-memory-grok-raw.md and H020-shadow-opus-review-raw.md. Exact IDs and
briefs in hypotheses/H020-memory-reviews.md. Opus completed, no pending children;
it read project records but fetched no external primary literature. Root checked
the algebra/counterexamples below. Cost review of the other cards remains live.
Verified improvement NONE; no numerical test admitted.

## Correct bookkeeping, missing shortcut

For W_t=e_t*(W_(t-1)+J_(s_(t-1))) with e_t in{±1}, let E=e_1...e_k.
Then

    W_k=E*(W_0+D),
    D=J_s0 + sum_(t=1)^(k-1) (e_1...e_t)*J_st.

This supports precomputed translation words and scalar-label updates. At most
r*(2r)^(k-1) such ordered keys suffice, before merging equal sums; the raw
(2r)^k upper bound is conservative. Per-target prefix construction and point,
label and lookup storage must all be paid. This identity alone supplies no way
to determine the correct word from a point more cheaply than executing it.

The raw proposal does not define its scale normalization, required state,
inverse-bit computation, update algorithm or error behavior. Its assumption
that canonical prime-field arithmetic can be followed by merely evaluating
integer formulas modulo2^w is false.

## Explicit paper counterexamples

For odd prime p>2^w+1, w>=1, take a=0, a'=2^w and b=p-2^w. The two a values
have identical low w bits. Their canonical prime-field sums are b (odd) and
0 (even), respectively. Reduction modulo p changes low bits through the
quotient times p. It is not just arithmetic modulo2^w.

At p=13,w=2, inputs2 and6 have the same low bits, but multiplication by7 gives
canonical results1 and3. Inputs1 and5 likewise share low bits, but their
prime-field inverses are1 and8. These are elementary modular calculations,
not experimental ECDLP evidence. Coprime additive-group orders also exclude
a nonzero homomorphism F_p -> Z/(2^w) preserving addition.

These refute universal low-bit field-operation simulation. They do NOT prove
that every specialized, nonhomomorphic predictor on valid EC points is
impossible. A predictor could read more state, exploit correlations, or have
controlled errors; it must actually be specified and costed. Projective
formulas by themselves do not produce the canonical affine parity/hash bits.
Infinity and cycle-escape rules need explicit handling as well.

## The claimed solve-time reduction is not established

Sampling only every kth point can miss a merged fine-walk path when the two
phases differ. Intermediate distinguished-point decisions or another paid
discovery mechanism must be included. The raw factor-k saving does not follow
from the word identity. Conversely, we do NOT accept the reviewer's categorical
fallback that every such macro-map necessarily needs sqrt(q) macro-steps:
the induced map and discovery schedule need their own analysis.

Cycle escapes involving doubling are not necessarily translations of the form
±W+D; minimum-point selection may require materialization. Table construction,
lookups, labels, all missed/failed words, replay, and final scalar verification
remain costs. The formula12*(w/log2(q))² is an assumed arithmetic proxy, not a
validated bit/word or hardware implementation. Fixed machine-word costs cannot
be erased by that ratio. For the illustrative B=2^20,k=4, setup below T/4 with
T=sqrt(pi*q/4) already requires q>64*B²/pi, about2^44.35; negligible setup is
a stronger condition. These numbers are arithmetic only.

## Why the proposed numerical falsifier is not executable

A32-bit state on a16-bit field can retain the entire coordinate, so agreement
there does not validate partial-coordinate prediction at larger sizes. More
fundamentally there is no specified shadow program to run. A median agreement
length does not measure complete-solver failure/recovery work. Failure of one
implementation/fixture also does not reject every field size or predictor.

Before testing, provide an executable shadow with declared inputs/state,
exact or probabilistic correctness, canonical indices/signs/intermediate
discovery flags, cycle/infinity handling, and a priced error detector/recovery.
Use a fixture whose coordinate width exceeds the retained state width and a
predeclared per-word error/work threshold. Compare total setup, shadow work,
lookup, detection and recovery with the same-resource baseline. No such
primitive or supported gain rationale is currently supplied. No new feature
sweep, Lean infrastructure or curve run is justified by this proposal.
